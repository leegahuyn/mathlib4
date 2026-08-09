#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
PVS = ROOT / "PrimalitySheafVerification"
HELPER_PATH = ROOT / "scripts" / "fa394_tournament_solver.py"
spec = importlib.util.spec_from_file_location("fa394_helper_for_fa396", HELPER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {HELPER_PATH}")
M = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = M
spec.loader.exec_module(M)

EVIDENCE = ROOT / "build-logs" / "fa396-proof-body"
STATE = EVIDENCE / "STATE.json"
NEXT = EVIDENCE / "NEXT_ACTION.json"
FINAL = EVIDENCE / "FINAL_STATUS.json"
MARKER = EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"

PREFERRED_MODELS = [
    "openai/gpt-5",
    "openai/gpt-5-mini",
    "openai/o3",
    "openai/o4-mini",
    "openai/gpt-4.1",
    "xai/grok-3-mini",
    "deepseek/DeepSeek-V3-0324",
    "mistral-ai/Mistral-Large-2411",
    "qwen/Qwen3-235B-A22B",
]


def load_json(path: Path, default: dict) -> dict:
    if not path.exists():
        return dict(default)
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else dict(default)
    except Exception:
        return dict(default)


def sha_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


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
    ordered = [m for m in PREFERRED_MODELS if m in available]
    ordered.extend(m for m in available if m not in ordered)
    return ordered or list(PREFERRED_MODELS)


def choose_models(models: list[str], cycle: int) -> list[str]:
    if len(models) <= 4:
        return models
    start = (cycle * 4) % len(models)
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


def top_level_declaration_bounds(source: str, first_line: int) -> tuple[int, int, str, str]:
    lines = source.splitlines(keepends=True)
    plain = [line.rstrip("\n") for line in lines]
    starts = [i for i, line in enumerate(plain) if M.H.DECL_RE.match(line)]
    if not starts:
        raise RuntimeError("no top-level declarations found")
    idx = max(0, min(len(lines) - 1, first_line - 1))
    prior = [s for s in starts if s <= idx]
    if not prior:
        start_line = starts[0]
        ordinal = 0
    else:
        start_line = prior[-1]
        ordinal = starts.index(start_line)
    end_line = starts[ordinal + 1] if ordinal + 1 < len(starts) else len(lines)
    start_char = sum(len(x) for x in lines[:start_line])
    end_char = sum(len(x) for x in lines[:end_line])
    segment = source[start_char:end_char]
    name_match = re.match(
        r"^(?:(?:noncomputable|private|protected|public|opaque)\s+)*"
        r"(?:theorem|lemma|corollary|def|abbrev|instance)"
        r"(?:\s+([A-Za-z0-9_'.]+))?",
        plain[start_line],
    )
    name = name_match.group(1) if name_match and name_match.group(1) else plain[start_line][:100]
    return start_char, end_char, name, segment


def find_assignment(segment: str) -> int | None:
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i + 1 < len(segment):
        if depth:
            if segment.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if segment.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if in_string:
            c = segment[i]
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
            continue
        if segment.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if segment.startswith("--", i):
            while i < len(segment) and segment[i] != "\n":
                i += 1
            continue
        if segment[i] == '"':
            in_string = True
            i += 1
            continue
        if segment.startswith(":=", i):
            return i
        i += 1
    return None


def extract_body(content: str) -> str | None:
    match = re.search(r"<BODY>\s*(.*?)\s*</BODY>", content, re.DOTALL)
    if not match:
        return None
    body = match.group(1)
    body = re.sub(r"^```(?:lean)?\s*\n", "", body)
    body = re.sub(r"\n```\s*$", "", body)
    if body and not body.endswith("\n"):
        body += "\n"
    return body


def neighbor_context(source: str, start_char: int, end_char: int, chars: int = 10000) -> str:
    lo = max(0, start_char - chars)
    hi = min(len(source), end_char + chars)
    return source[lo:hi]


def make_prompt(
    path: Path,
    metric,
    log_text: str,
    source: str,
    declaration_name: str,
    segment: str,
    assignment: int,
    start_char: int,
    end_char: int,
    round_index: int,
) -> str:
    prefix = segment[: assignment + 2]
    old_body = segment[assignment + 2 :]
    errors = M.H.log_context(log_text, radius=150)
    nearby = neighbor_context(source, start_char, end_char, chars=14000 if round_index % 3 == 0 else 8000)
    api = M.H.exact_api_search(segment, errors, max_chars=24000)
    return f"""Repair only the body of the earliest failing Lean declaration.

File: {path.relative_to(ROOT)}
Declaration: {declaration_name}
Robust metric:
{json.dumps(metric.to_json(), indent=2)}

The declaration header and assignment prefix below are immutable. Your output replaces
only the text after `:=` up to the next top-level declaration.

<IMMUTABLE_PREFIX>
{prefix}
</IMMUTABLE_PREFIX>

<CURRENT_BODY>
{old_body}
</CURRENT_BODY>

<COMPILER_ERRORS>
{errors}
</COMPILER_ERRORS>

<NEARBY_SOURCE_CONTEXT>
{nearby}
</NEARBY_SOURCE_CONTEXT>

<EXACT_API_SEARCH>
{api}
</EXACT_API_SEARCH>

Return exactly one block:
<BODY>
replacement text that comes immediately after the immutable `:=`
</BODY>

Rules:
- The replacement normally begins with `by` for proofs.
- Do not repeat the declaration header or `:=`.
- Do not change assumptions, conclusion, binders, declaration name, or type.
- You may use local `have`, `let`, `letI`, `change`, `show`, `calc`, `simpa only`, and
  existing current Mathlib/project lemmas.
- No sorry, admit, new axiom, unsafe, native_decide, or Lean.ofReduceBool.
- Fix the first root API/typeclass/dependent-transport error, not later cascades.
- Output tags only, without markdown or explanation.
"""


def fetch_sources(cycle: int) -> dict[str, str]:
    branches = {
        "pass391": "fix/fa391-final-gate-20260809",
        "pass394": "fix/fa394-tournament-20260809",
        "pass395": "fix/fa395-persistent-tournament-20260809",
        "pr9": "ci/fa319-isolated-20260807",
    }
    result: dict[str, str] = {}
    for label, branch in branches.items():
        source = M.fetch_branch_source(branch, f"fa396-{cycle}-{label}")
        if source is not None:
            result[label] = source
    return result


def repair_body(
    path: Path,
    evidence: Path,
    token: str,
    models: list[str],
    *,
    rounds: int,
    max_candidates: int,
    max_errors: int,
):
    evidence.mkdir(parents=True, exist_ok=True)
    source = path.read_text(encoding="utf-8")
    baseline_headers = M.H.declaration_headers(source)
    lean_metric = M.H.compile_file(path, evidence / "round-000-baseline.log", max_errors=max_errors, timeout=1800)
    metric = M.robust_metric(source, lean_metric)
    history = [{"round": 0, "metric": metric.to_json()}]
    (evidence / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
    if metric.passed:
        return metric

    no_progress = 0
    for round_index in range(1, rounds + 1):
        source = path.read_text(encoding="utf-8")
        log_path = evidence / (
            "round-000-baseline.log" if round_index == 1 else f"round-{round_index - 1:03d}-accepted.log"
        )
        if not log_path.exists():
            log_path = evidence / "round-000-baseline.log"
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
        try:
            start, end, name, segment = top_level_declaration_bounds(source, metric.lean.first_line)
        except Exception as exc:
            history.append({"round": round_index, "accepted": False, "reason": repr(exc)})
            break
        assignment = find_assignment(segment)
        if assignment is None:
            history.append({"round": round_index, "accepted": False, "reason": "no := in failing declaration"})
            break
        prompt = make_prompt(
            path, metric, log_text, source, name, segment, assignment, start, end, round_index
        )
        (evidence / f"round-{round_index:03d}-prompt.txt").write_text(prompt, encoding="utf-8")

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

        candidates: list[tuple[str, str]] = []
        seen: set[str] = set()
        immutable = segment[: assignment + 2]
        for model, seed, content in responses:
            safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", model)
            (evidence / f"round-{round_index:03d}-response-{safe}-{seed}.txt").write_text(
                content, encoding="utf-8"
            )
            body = extract_body(content)
            if body is None:
                continue
            if body.startswith(":="):
                body = body[2:].lstrip()
            replacement = immutable + (" " if body and not body.startswith((" ", "\n")) else "") + body
            candidate = source[:start] + replacement + source[end:]
            digest = sha_text(candidate)
            if digest in seen or candidate == source:
                continue
            seen.add(digest)
            candidates.append((f"{safe}-{seed}-{digest[:10]}", candidate))
        candidates.sort(key=lambda item: abs(len(item[1]) - len(source)))
        candidates = candidates[:max_candidates]

        diagnostics = []
        best_metric = None
        best_source = None
        original = path.read_text(encoding="utf-8")
        for idx, (label, candidate) in enumerate(candidates):
            if M.H.declaration_headers(candidate) != baseline_headers:
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
                    evidence / f"round-{round_index:03d}-candidate-{idx:02d}.log",
                    max_errors=max_errors,
                    timeout=1800,
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
        (evidence / f"round-{round_index:03d}-candidates.json").write_text(
            json.dumps(diagnostics, indent=2), encoding="utf-8"
        )

        if best_metric is None or best_source is None:
            no_progress += 1
            history.append(
                {
                    "round": round_index,
                    "accepted": False,
                    "candidate_count": len(candidates),
                    "metric": metric.to_json(),
                }
            )
            (evidence / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
            if no_progress >= 3:
                break
            continue

        no_progress = 0
        path.write_text(best_source, encoding="utf-8")
        accepted_lean = M.H.compile_file(
            path,
            evidence / f"round-{round_index:03d}-accepted.log",
            max_errors=max_errors,
            timeout=1800,
        )
        metric = M.robust_metric(best_source, accepted_lean)
        history.append({"round": round_index, "accepted": True, "metric": metric.to_json()})
        (evidence / "history.json").write_text(json.dumps(history, indent=2), encoding="utf-8")
        (evidence / "best-source.lean").write_text(best_source, encoding="utf-8")
        if metric.passed:
            break
    return metric


def source_hashes() -> dict[str, str]:
    paths = [
        PVS / "Mock2_FunctionalAnalysis.lean",
        PVS / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PVS.glob("Mock3*.lean")),
        PVS / "QYM.lean",
    ]
    return {str(path.relative_to(ROOT)): M.H.sha256_file(path) for path in paths if path.exists()}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-cycles", type=int, default=16)
    parser.add_argument("--max-errors", type=int, default=220)
    args = parser.parse_args()
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    state = load_json(STATE, {"cycle": 0, "history": []})
    cycle = int(state.get("cycle", 0))
    if cycle >= args.max_cycles:
        NEXT.write_text(json.dumps({"dispatch": False, "reason": "max_cycles"}, indent=2))
        return 2

    all_models = catalog_models(token)
    models = choose_models(all_models, cycle)
    before = source_hashes()
    M.EVIDENCE = EVIDENCE / f"cycle-{cycle:03d}"
    fa = PVS / "Mock2_FunctionalAnalysis.lean"
    _, selected_metric, selected_label = M.select_best_baseline(
        fa,
        M.EVIDENCE / "tournament",
        fetch_sources(cycle),
        max_errors=args.max_errors,
    )
    body_metric = repair_body(
        fa,
        M.EVIDENCE / "Mock2_FunctionalAnalysis-body",
        token,
        models,
        rounds=5,
        max_candidates=5,
        max_errors=args.max_errors,
    )

    if body_metric.passed:
        summary = M.verify_ordered(
            token,
            models,
            fa_rounds=1,
            downstream_rounds=8,
            max_candidates=5,
            max_errors=args.max_errors,
        )
    else:
        summary = {
            "complete": False,
            "stage": "Mock2_FunctionalAnalysis",
            "reason": "proof-body solver did not reach exit code 0",
            "fa_metric": body_metric.to_json(),
            "modules": [],
        }
    summary["cycle"] = cycle
    summary["models"] = models
    summary["tournament_selected"] = selected_label
    summary["tournament_selected_metric"] = selected_metric.to_json()
    after = source_hashes()
    changed = before != after
    complete = bool(summary.get("complete"))
    if complete:
        summary["status"] = "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS"
        MARKER.write_text("SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS\n", encoding="utf-8")

    history = list(state.get("history", []))
    history.append(
        {
            "cycle": cycle,
            "selected": selected_label,
            "selected_metric": selected_metric.to_json(),
            "body_metric": body_metric.to_json(),
            "source_changed": changed,
            "complete": complete,
            "stage": summary.get("stage"),
            "reason": summary.get("reason"),
            "models": models,
            "before": before,
            "after": after,
        }
    )
    STATE.write_text(json.dumps({"cycle": cycle + 1, "history": history[-40:]}, indent=2), encoding="utf-8")
    FINAL.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    dispatch = not complete and cycle + 1 < args.max_cycles
    NEXT.write_text(
        json.dumps(
            {
                "dispatch": dispatch,
                "complete": complete,
                "next_cycle": cycle + 1,
                "source_changed": changed,
                "stage": summary.get("stage"),
                "reason": summary.get("reason"),
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    return 0 if complete else 2


if __name__ == "__main__":
    raise SystemExit(main())
