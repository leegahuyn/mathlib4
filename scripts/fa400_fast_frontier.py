#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
PVS = ROOT / "PrimalitySheafVerification"
HELPER_PATH = ROOT / "scripts" / "fa394_tournament_solver.py"
spec = importlib.util.spec_from_file_location("fa394_helper_for_fa400", HELPER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {HELPER_PATH}")
M = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = M
spec.loader.exec_module(M)

EVIDENCE = ROOT / "build-logs" / "fa400-fast-frontier"
STATE = EVIDENCE / "STATE.json"
FINAL = EVIDENCE / "FINAL_STATUS.json"
MARKER = EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"
BRANCH = os.environ.get("FA400_BRANCH", "fix/fa400-fast-frontier-20260809")

PREFERRED_MODELS = [
    "openai/gpt-5", "openai/gpt-5-mini", "openai/o3", "openai/o4-mini",
    "openai/gpt-4.1", "xai/grok-3-mini", "deepseek/DeepSeek-V3-0324",
    "mistral-ai/Mistral-Large-2411", "qwen/Qwen3-235B-A22B",
]


def catalog_models(token: str) -> list[str]:
    request = urllib.request.Request(
        "https://models.github.ai/catalog/models",
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    available: list[str] = []
    try:
        with urllib.request.urlopen(request, timeout=90) as response:
            payload = json.loads(response.read().decode())
        entries = payload if isinstance(payload, list) else payload.get("models", [])
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            model_id = entry.get("id") or entry.get("name")
            task = str(entry.get("task", "")).lower()
            if model_id and (not task or "chat" in task or "completion" in task):
                available.append(str(model_id))
    except Exception:
        pass
    ordered = [model for model in PREFERRED_MODELS if model in available]
    ordered.extend(model for model in available if model not in ordered)
    return ordered or list(PREFERRED_MODELS)


def choose_models(models: list[str], round_index: int) -> list[str]:
    if len(models) <= 4:
        return models
    start = (round_index * 3) % len(models)
    rotated = models[start:] + models[:start]
    selected: list[str] = []
    publishers: set[str] = set()
    for model in rotated:
        publisher = model.split("/", 1)[0]
        if publisher not in publishers or len(selected) >= 2:
            selected.append(model)
            publishers.add(publisher)
        if len(selected) == 4:
            break
    return selected


def fetch_sources() -> dict[str, str]:
    branches = {
        "pass391": "fix/fa391-final-gate-20260809",
        "pass394": "fix/fa394-tournament-20260809",
        "pass395": "fix/fa395-persistent-tournament-20260809",
        "pass396": "fix/fa396-proof-body-persistent-20260809",
        "pass398": "fix/fa398-single-run-tournament-loop-20260809",
        "pass399": "fix/fa399-single-run-proof-body-loop-20260809",
        "pr9": "ci/fa319-isolated-20260807",
    }
    result: dict[str, str] = {}
    for label, branch in branches.items():
        source = M.fetch_branch_source(branch, f"fa400-{label}")
        if source is not None:
            result[label] = source
    return result


def git_commit_progress(round_index: int, metric) -> None:
    STATE.parent.mkdir(parents=True, exist_ok=True)
    STATE.write_text(
        json.dumps(
            {
                "round": round_index,
                "metric": metric.to_json(),
                "source_sha256": M.H.sha256_file(PVS / "Mock2_FunctionalAnalysis.lean"),
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    subprocess.run(
        ["git", "add", "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean", str(STATE.relative_to(ROOT))],
        cwd=ROOT,
        check=True,
    )
    diff = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=ROOT)
    if diff.returncode == 0:
        return
    subprocess.run(
        ["git", "commit", "-m", f"fix: advance PASS 400 frontier round {round_index}"],
        cwd=ROOT,
        check=True,
    )
    subprocess.run(["git", "push", "origin", f"HEAD:{BRANCH}"], cwd=ROOT, check=True)


def query_candidates(
    source: str,
    metric,
    log_text: str,
    token: str,
    models: list[str],
    round_index: int,
) -> list[tuple[str, str]]:
    prompt, start, end = M.build_prompt(
        PVS / "Mock2_FunctionalAnalysis.lean", source, metric, log_text, round_index
    )
    prompt += "\nCandidate screening uses maxErrors=1 and accepts only movement to a later top-level declaration. Solve the whole current failing declaration if necessary.\n"
    (EVIDENCE / f"round-{round_index:03d}-prompt.txt").write_text(prompt, encoding="utf-8")
    jobs = [(model, seed) for model in models for seed in range(2)]
    responses: list[tuple[str, int, str]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(10, len(jobs))) as pool:
        futures = {
            pool.submit(M.H.model_request, model, prompt, token, seed): (model, seed)
            for model, seed in jobs
        }
        for future in concurrent.futures.as_completed(futures):
            model, seed = futures[future]
            try:
                _, content = future.result()
            except Exception as exc:
                content = f"<ERROR>{exc!r}</ERROR>"
            responses.append((model, seed, content))

    result: list[tuple[str, str]] = []
    seen: set[str] = set()
    for model, seed, content in responses:
        safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", model)
        (EVIDENCE / f"round-{round_index:03d}-response-{safe}-{seed}.txt").write_text(
            content, encoding="utf-8"
        )
        for candidate in M.response_candidates(source, content, start, end):
            digest = M.H.sha256_bytes(candidate.encode())
            if digest in seen or candidate == source:
                continue
            seen.add(digest)
            result.append((f"{safe}-{seed}-{digest[:10]}", candidate))
    result.sort(key=lambda item: abs(len(item[1]) - len(source)))
    return result


def fast_repair(token: str, all_models: list[str], max_rounds: int, max_candidates: int):
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    path = PVS / "Mock2_FunctionalAnalysis.lean"
    source = path.read_text(encoding="utf-8")
    headers = M.H.declaration_headers(source)
    lean = M.H.compile_file(path, EVIDENCE / "round-000-baseline.log", max_errors=1, timeout=1200)
    metric = M.robust_metric(source, lean)
    history = [{"round": 0, "metric": metric.to_json()}]
    (EVIDENCE / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
    if metric.passed:
        return metric

    no_progress = 0
    for round_index in range(1, max_rounds + 1):
        source = path.read_text(encoding="utf-8")
        log_path = EVIDENCE / (
            "round-000-baseline.log" if round_index == 1 else f"round-{round_index - 1:03d}-accepted.log"
        )
        if not log_path.exists():
            log_path = EVIDENCE / "round-000-baseline.log"
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
        models = choose_models(all_models, round_index)
        candidates = query_candidates(source, metric, log_text, token, models, round_index)
        candidates = candidates[:max_candidates]
        diagnostics = []
        best_metric = None
        best_source = None
        original = source
        for idx, (label, candidate) in enumerate(candidates):
            if M.H.declaration_headers(candidate) != headers:
                diagnostics.append({"label": label, "rejected": "public headers changed"})
                continue
            bad = M.H.forbidden_counts(candidate)
            if any(bad.values()):
                diagnostics.append({"label": label, "rejected": f"forbidden {bad}"})
                continue
            path.write_text(candidate, encoding="utf-8")
            try:
                cand_lean = M.H.compile_file(
                    path,
                    EVIDENCE / f"round-{round_index:03d}-candidate-{idx:02d}.log",
                    max_errors=1,
                    timeout=1200,
                )
                cand_metric = M.robust_metric(candidate, cand_lean)
            finally:
                path.write_text(original, encoding="utf-8")
            diagnostics.append({"label": label, "metric": cand_metric.to_json()})
            if cand_metric.better_than(metric) and (
                best_metric is None or cand_metric.better_than(best_metric)
            ):
                best_metric = cand_metric
                best_source = candidate
        (EVIDENCE / f"round-{round_index:03d}-candidates.json").write_text(
            json.dumps(diagnostics, indent=2), encoding="utf-8"
        )

        if best_metric is None or best_source is None:
            no_progress += 1
            history.append({"round": round_index, "accepted": False, "metric": metric.to_json()})
            (EVIDENCE / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
            if no_progress >= 4:
                break
            continue

        no_progress = 0
        path.write_text(best_source, encoding="utf-8")
        accepted_lean = M.H.compile_file(
            path, EVIDENCE / f"round-{round_index:03d}-accepted.log", max_errors=1, timeout=1200
        )
        metric = M.robust_metric(best_source, accepted_lean)
        history.append({"round": round_index, "accepted": True, "metric": metric.to_json()})
        (EVIDENCE / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
        (EVIDENCE / "best-source.lean").write_text(best_source, encoding="utf-8")
        git_commit_progress(round_index, metric)
        if metric.passed:
            break
    return metric


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rounds", type=int, default=14)
    parser.add_argument("--candidates", type=int, default=4)
    args = parser.parse_args()
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    fa = PVS / "Mock2_FunctionalAnalysis.lean"
    M.EVIDENCE = EVIDENCE / "ordered"
    _, selected_metric, selected_label = M.select_best_baseline(
        fa, EVIDENCE / "tournament", fetch_sources(), max_errors=1
    )
    git_commit_progress(0, selected_metric)

    models = catalog_models(token)
    frontier = fast_repair(token, models, args.rounds, args.candidates)
    full = M.H.compile_file(fa, EVIDENCE / "full-frontier.log", max_errors=300, timeout=1800)
    summary: dict[str, object] = {
        "complete": False,
        "stage": "Mock2_FunctionalAnalysis",
        "tournament_selected": selected_label,
        "tournament_metric": selected_metric.to_json(),
        "frontier_metric": frontier.to_json(),
        "full_metric": full.to_json(),
    }
    if full.passed:
        ordered = M.verify_ordered(
            token,
            choose_models(models, 99),
            fa_rounds=1,
            downstream_rounds=10,
            max_candidates=5,
            max_errors=250,
        )
        summary.update(ordered)
    else:
        summary["reason"] = "full FA compile still fails after fast frontier rounds"
    FINAL.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    subprocess.run(["git", "add", str(FINAL.relative_to(ROOT))], cwd=ROOT, check=True)
    if summary.get("complete"):
        MARKER.write_text("SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS\n", encoding="utf-8")
        subprocess.run(["git", "add", str(MARKER.relative_to(ROOT))], cwd=ROOT, check=True)
    if subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=ROOT).returncode != 0:
        subprocess.run(["git", "commit", "-m", "ci: record PASS 400 final status"], cwd=ROOT, check=True)
        subprocess.run(["git", "push", "origin", f"HEAD:{BRANCH}"], cwd=ROOT, check=True)
    return 0 if summary.get("complete") else 2


if __name__ == "__main__":
    raise SystemExit(main())
