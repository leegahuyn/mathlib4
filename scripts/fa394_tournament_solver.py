#!/usr/bin/env python3
from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Sequence

ROOT = Path(__file__).resolve().parents[1]
PVS = ROOT / "PrimalitySheafVerification"
EVIDENCE = ROOT / "build-logs" / "fa394-tournament"
HELPER_PATH = ROOT / "scripts" / "fa392_iterative_solver.py"

spec = importlib.util.spec_from_file_location("fa392_helper_for_fa394", HELPER_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import helper {HELPER_PATH}")
H = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = H
spec.loader.exec_module(H)


@dataclasses.dataclass(frozen=True)
class RobustMetric:
    lean: H.Metric
    declaration_ordinal: int
    declaration_name: str

    @property
    def passed(self) -> bool:
        return self.lean.passed

    def score(self) -> tuple[int, int, int]:
        if self.passed:
            return (2, 10**9, 0)
        return (1, self.declaration_ordinal, -self.lean.errors)

    def better_than(self, other: "RobustMetric") -> bool:
        return self.score() > other.score()

    def to_json(self) -> dict[str, object]:
        return {
            "lean": self.lean.to_json(),
            "declaration_ordinal": self.declaration_ordinal,
            "declaration_name": self.declaration_name,
            "score": self.score(),
        }


def git(*args: str, timeout: int = 180) -> subprocess.CompletedProcess[str]:
    return H.run(["git", *args], timeout=timeout)


def declaration_identity(source: str, first_line: int) -> tuple[int, str]:
    lines = source.splitlines()
    starts = [i for i, line in enumerate(lines) if H.DECL_RE.match(line)]
    if first_line <= 0 or not starts:
        return (-1, "(unknown)")
    idx = max(0, min(len(lines) - 1, first_line - 1))
    prior = [i for i in starts if i <= idx]
    if not prior:
        return (-1, "(preamble)")
    start = prior[-1]
    ordinal = starts.index(start)
    line = lines[start]
    m = re.match(
        r"^(?:(?:noncomputable|private|protected|public|opaque)\s+)*"
        r"(?:theorem|lemma|corollary|def|abbrev|instance|structure|class|inductive)"
        r"(?:\s+([A-Za-z0-9_'.]+))?",
        line,
    )
    return ordinal, (m.group(1) if m and m.group(1) else line[:120])


def robust_metric(source: str, metric: H.Metric) -> RobustMetric:
    if metric.passed:
        return RobustMetric(metric, 10**9, "(passed)")
    ordinal, name = declaration_identity(source, metric.first_line)
    return RobustMetric(metric, ordinal, name)


def compile_source(
    path: Path,
    source: str,
    log_path: Path,
    *,
    max_errors: int,
) -> RobustMetric:
    original = path.read_text(encoding="utf-8")
    path.write_text(source, encoding="utf-8")
    try:
        metric = H.compile_file(path, log_path, max_errors=max_errors, timeout=1800)
        return robust_metric(source, metric)
    finally:
        path.write_text(original, encoding="utf-8")


def fetch_branch_source(branch: str, label: str) -> str | None:
    remote_ref = f"refs/remotes/origin/fa394-{label}"
    proc = git(
        "fetch", "--no-tags", "--force", "origin",
        f"refs/heads/{branch}:{remote_ref}",
        timeout=300,
    )
    if proc.returncode != 0:
        return None
    shown = git(
        "show",
        f"{remote_ref}:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
        timeout=120,
    )
    if shown.returncode != 0 or not shown.stdout.strip():
        return None
    return shown.stdout


def select_best_baseline(
    path: Path,
    evidence: Path,
    branch_candidates: dict[str, str],
    *,
    max_errors: int,
) -> tuple[str, RobustMetric, str]:
    evidence.mkdir(parents=True, exist_ok=True)
    original = path.read_text(encoding="utf-8")
    baseline_headers = H.declaration_headers(original)
    candidates: dict[str, str] = {"current": original}
    candidates.update(branch_candidates)

    records: list[dict[str, object]] = []
    best_label = "current"
    best_source = original
    best_metric: RobustMetric | None = None
    seen: set[str] = set()

    for label, source in candidates.items():
        digest = H.sha256_bytes(source.encode())
        if digest in seen:
            continue
        seen.add(digest)
        if H.declaration_headers(source) != baseline_headers:
            records.append({"label": label, "sha256": digest, "rejected": "public headers differ"})
            continue
        bad = H.forbidden_counts(source)
        if any(bad.values()):
            records.append({"label": label, "sha256": digest, "rejected": f"forbidden {bad}"})
            continue
        metric = compile_source(
            path,
            source,
            evidence / f"baseline-{label}.log",
            max_errors=max_errors,
        )
        records.append({"label": label, "sha256": digest, "metric": metric.to_json()})
        if best_metric is None or metric.better_than(best_metric):
            best_metric = metric
            best_source = source
            best_label = label

    if best_metric is None:
        raise RuntimeError("no admissible tournament baseline")
    path.write_text(best_source, encoding="utf-8")
    (evidence / "baseline-selection.json").write_text(
        json.dumps(
            {
                "selected": best_label,
                "selected_sha256": H.sha256_bytes(best_source.encode()),
                "selected_metric": best_metric.to_json(),
                "candidates": records,
            },
            indent=2,
        )
    )
    return best_source, best_metric, best_label


def slice_bounds(source: str, first_line: int, radius_declarations: int) -> tuple[int, int, str]:
    lines = source.splitlines(keepends=True)
    plain = [line.rstrip("\n") for line in lines]
    starts = [i for i, line in enumerate(plain) if H.DECL_RE.match(line)]
    idx = max(0, min(len(lines) - 1, first_line - 1))
    prior = [i for i in starts if i <= idx]
    if prior:
        current = prior[-1]
        pos = starts.index(current)
        start_line = starts[max(0, pos - radius_declarations)]
        end_line = starts[pos + 2] if pos + 2 < len(starts) else len(lines)
    else:
        start_line = max(0, idx - 240)
        end_line = min(len(lines), idx + 300)
    start_char = sum(len(x) for x in lines[:start_line])
    end_char = sum(len(x) for x in lines[:end_line])
    return start_char, end_char, source[start_char:end_char]


def extract_replacement(content: str) -> str | None:
    m = re.search(r"<REPLACEMENT>\s*(.*?)\s*</REPLACEMENT>", content, re.DOTALL)
    if not m:
        return None
    value = m.group(1)
    value = re.sub(r"^```(?:lean)?\s*\n", "", value)
    value = re.sub(r"\n```\s*$", "", value)
    if value and not value.endswith("\n"):
        value += "\n"
    return value


def build_prompt(
    path: Path,
    source: str,
    metric: RobustMetric,
    log_text: str,
    round_index: int,
) -> tuple[str, int, int]:
    first_line = metric.lean.first_line if metric.lean.first_line > 0 else 1
    radius = 4 if round_index % 3 == 0 else 2
    start, end, block = slice_bounds(source, first_line, radius)
    errors = H.log_context(log_text, radius=160 if radius == 4 else 100)
    api = H.exact_api_search(block, errors, max_chars=24000)
    prompt = f"""Repair the earliest independent Lean 4 error in:
{path.relative_to(ROOT)}

Robust compiler metric:
{json.dumps(metric.to_json(), indent=2)}

The metric compares the ordinal/name of the first failing top-level declaration, not only
physical line numbers. Adding blank lines cannot count as progress.

<ERROR_CONTEXT>
{errors}
</ERROR_CONTEXT>

<EXACT_SOURCE_SLICE>
{block}
</EXACT_SOURCE_SLICE>

<EXACT_API_SEARCH>
{api}
</EXACT_API_SEARCH>

Return either exact edits:
<EDIT>
<OLD>
byte-for-byte existing text
</OLD>
<NEW>
replacement text
</NEW>
</EDIT>

or one replacement for the whole source slice:
<REPLACEMENT>
corrected full slice
</REPLACEMENT>

Rules:
- Preserve every existing public theorem/lemma/corollary/def/abbrev header byte-for-byte.
- Never change assumptions or conclusions.
- Private helper lemmas and local instances are allowed.
- No sorry, admit, axiom, unsafe, native_decide, or Lean.ofReduceBool.
- Prefer explicit typed `letI`, `change`, `show`, `simpa only`, and current Mathlib API.
- Fix the root declaration/typeclass/API issue, not downstream cascade diagnostics.
- Output tags only; no explanation or markdown.
"""
    return prompt, start, end


def response_candidates(
    source: str,
    content: str,
    slice_start: int,
    slice_end: int,
) -> list[str]:
    result: list[str] = []
    edits = H.extract_edits(content)
    if edits:
        edited = H.apply_edits(source, edits)
        if edited is not None and edited != source:
            result.append(edited)
    replacement = extract_replacement(content)
    if replacement is not None:
        candidate = source[:slice_start] + replacement + source[slice_end:]
        if candidate != source:
            result.append(candidate)
    return result


def query_models(
    prompt: str,
    token: str,
    models: Sequence[str],
    evidence: Path,
    round_index: int,
) -> list[tuple[str, str]]:
    jobs = [(model, seed) for model in models for seed in range(2)]
    responses: list[tuple[str, str]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(10, len(jobs))) as pool:
        futures = {
            pool.submit(H.model_request, model, prompt, token, seed): (model, seed)
            for model, seed in jobs
        }
        for future in concurrent.futures.as_completed(futures):
            model, seed = futures[future]
            try:
                _, content = future.result()
            except Exception as exc:
                content = f"<ERROR>{exc!r}</ERROR>"
            safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", model)
            label = f"{safe}-{seed}"
            (evidence / f"round-{round_index:03d}-response-{label}.txt").write_text(
                content, encoding="utf-8"
            )
            responses.append((label, content))
    return responses


def repair_target(
    path: Path,
    evidence: Path,
    *,
    token: str,
    models: Sequence[str],
    max_rounds: int,
    max_candidates: int,
    max_errors: int,
) -> RobustMetric:
    evidence.mkdir(parents=True, exist_ok=True)
    source = path.read_text(encoding="utf-8")
    baseline_headers = H.declaration_headers(source)
    initial = H.compile_file(path, evidence / "round-000-baseline.log", max_errors=max_errors, timeout=1800)
    metric = robust_metric(source, initial)
    history: list[dict[str, object]] = [{"round": 0, "metric": metric.to_json()}]
    (evidence / "history.json").write_text(json.dumps(history, indent=2))
    if metric.passed:
        return metric

    no_progress_rounds = 0
    for round_index in range(1, max_rounds + 1):
        source = path.read_text(encoding="utf-8")
        prev_log = evidence / (
            "round-000-baseline.log" if round_index == 1 else f"round-{round_index - 1:03d}-accepted.log"
        )
        if not prev_log.exists():
            prev_log = evidence / "round-000-baseline.log"
        log_text = prev_log.read_text(encoding="utf-8", errors="replace")
        prompt, slice_start, slice_end = build_prompt(path, source, metric, log_text, round_index)
        (evidence / f"round-{round_index:03d}-prompt.txt").write_text(prompt, encoding="utf-8")
        responses = query_models(prompt, token, models, evidence, round_index)

        candidates: list[tuple[str, str]] = []
        seen: set[str] = set()
        for label, content in responses:
            for candidate in response_candidates(source, content, slice_start, slice_end):
                digest = H.sha256_bytes(candidate.encode())
                if digest in seen:
                    continue
                seen.add(digest)
                candidates.append((f"{label}-{digest[:10]}", candidate))
        candidates.sort(key=lambda item: abs(len(item[1]) - len(source)))
        candidates = candidates[:max_candidates]

        diagnostics: list[dict[str, object]] = []
        best_metric: RobustMetric | None = None
        best_source: str | None = None
        for idx, (label, candidate) in enumerate(candidates):
            if H.declaration_headers(candidate) != baseline_headers:
                diagnostics.append({"label": label, "rejected": "public headers changed"})
                continue
            bad = H.forbidden_counts(candidate)
            if any(bad.values()):
                diagnostics.append({"label": label, "rejected": f"forbidden {bad}"})
                continue
            cand_metric = compile_source(
                path,
                candidate,
                evidence / f"round-{round_index:03d}-candidate-{idx:02d}.log",
                max_errors=max_errors,
            )
            diagnostics.append({"label": label, "metric": cand_metric.to_json()})
            if cand_metric.better_than(metric) and (
                best_metric is None or cand_metric.better_than(best_metric)
            ):
                best_metric = cand_metric
                best_source = candidate
        (evidence / f"round-{round_index:03d}-candidates.json").write_text(
            json.dumps(diagnostics, indent=2)
        )

        if best_metric is None or best_source is None:
            no_progress_rounds += 1
            history.append(
                {
                    "round": round_index,
                    "accepted": False,
                    "candidate_count": len(candidates),
                    "metric": metric.to_json(),
                }
            )
            (evidence / "history.json").write_text(json.dumps(history, indent=2))
            if no_progress_rounds >= 3:
                break
            continue

        no_progress_rounds = 0
        path.write_text(best_source, encoding="utf-8")
        accepted_lean = H.compile_file(
            path,
            evidence / f"round-{round_index:03d}-accepted.log",
            max_errors=max_errors,
            timeout=1800,
        )
        metric = robust_metric(best_source, accepted_lean)
        history.append({"round": round_index, "accepted": True, "metric": metric.to_json()})
        (evidence / "history.json").write_text(json.dumps(history, indent=2))
        (evidence / "best-source.lean").write_text(best_source, encoding="utf-8")
        if metric.passed:
            break
    return metric


def verify_ordered(
    token: str,
    models: Sequence[str],
    *,
    fa_rounds: int,
    downstream_rounds: int,
    max_candidates: int,
    max_errors: int,
) -> dict[str, object]:
    summary: dict[str, object] = {
        "complete": False,
        "stage": "Mock2_FunctionalAnalysis",
        "modules": [],
    }
    fa = PVS / "Mock2_FunctionalAnalysis.lean"
    fa_metric = repair_target(
        fa,
        EVIDENCE / "Mock2_FunctionalAnalysis",
        token=token,
        models=models,
        max_rounds=fa_rounds,
        max_candidates=max_candidates,
        max_errors=max_errors,
    )
    summary["fa_metric"] = fa_metric.to_json()
    if not fa_metric.passed:
        summary["reason"] = "FA did not compile"
        return summary

    ok, metrics = H.verify_twice(fa, EVIDENCE / "Mock2_FunctionalAnalysis" / "two-pass", max_errors)
    summary["modules"].append(
        {"module": fa.name, "status": "PASS_2X" if ok else "FAIL", "runs": [m.to_json() for m in metrics]}
    )
    if not ok:
        summary["reason"] = "FA independent two-pass verification failed"
        return summary

    targets = [
        PVS / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PVS.glob("Mock3*.lean")),
        PVS / "QYM.lean",
    ]
    for target in targets:
        if not target.exists():
            continue
        summary["stage"] = target.name
        metric = repair_target(
            target,
            EVIDENCE / target.stem,
            token=token,
            models=models,
            max_rounds=downstream_rounds,
            max_candidates=max_candidates,
            max_errors=max_errors,
        )
        if not metric.passed:
            summary["modules"].append({"module": target.name, "status": "FAIL", "metric": metric.to_json()})
            summary["reason"] = f"{target.name} did not compile"
            return summary
        ok, runs = H.verify_twice(target, EVIDENCE / target.stem / "two-pass", max_errors)
        summary["modules"].append(
            {"module": target.name, "status": "PASS_2X" if ok else "FAIL", "runs": [m.to_json() for m in runs]}
        )
        if not ok:
            summary["reason"] = f"{target.name} independent two-pass verification failed"
            return summary

    audited = [
        fa,
        PVS / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PVS.glob("Mock3*.lean")),
        PVS / "QYM.lean",
    ]
    audit = {
        str(path.relative_to(ROOT)): H.forbidden_counts(path.read_text(encoding="utf-8"))
        for path in audited
        if path.exists()
    }
    (EVIDENCE / "FINAL_FORBIDDEN_AUDIT.json").write_text(json.dumps(audit, indent=2))
    if any(any(counts.values()) for counts in audit.values()):
        summary["reason"] = "final forbidden-token audit failed"
        return summary

    summary["complete"] = True
    summary["stage"] = "complete"
    summary["status"] = "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS"
    summary["sources"] = {
        str(path.relative_to(ROOT)): H.sha256_file(path)
        for path in audited
        if path.exists()
    }
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--fa-rounds", type=int, default=14)
    parser.add_argument("--downstream-rounds", type=int, default=8)
    parser.add_argument("--max-candidates", type=int, default=4)
    parser.add_argument("--max-errors", type=int, default=200)
    args = parser.parse_args()

    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        raise SystemExit("GITHUB_TOKEN is required")
    models = [
        x.strip()
        for x in os.environ.get(
            "FA394_MODELS",
            "openai/gpt-5,openai/o3,openai/o4-mini,openai/gpt-4.1,"
            "xai/grok-3-mini,deepseek/DeepSeek-V3-0324,"
            "mistral-ai/Mistral-Large-2411,qwen/Qwen3-235B-A22B",
        ).split(",")
        if x.strip()
    ]
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    fa = PVS / "Mock2_FunctionalAnalysis.lean"
    baseline_candidates: dict[str, str] = {}
    branch_map = {
        "pass391": "fix/fa391-final-gate-20260809",
        "pass392": "fix/fa392-iterative-solver-20260809",
        "pass393v2": "fix/fa393-v2-declaration-replacement-20260809",
    }
    for label, branch in branch_map.items():
        source = fetch_branch_source(branch, label)
        if source is not None:
            baseline_candidates[label] = source

    _, selected_metric, selected_label = select_best_baseline(
        fa,
        EVIDENCE / "tournament",
        baseline_candidates,
        max_errors=args.max_errors,
    )
    summary = verify_ordered(
        token,
        models,
        fa_rounds=args.fa_rounds,
        downstream_rounds=args.downstream_rounds,
        max_candidates=args.max_candidates,
        max_errors=args.max_errors,
    )
    summary["tournament_selected"] = selected_label
    summary["tournament_selected_metric"] = selected_metric.to_json()
    (EVIDENCE / "FINAL_STATUS.json").write_text(json.dumps(summary, indent=2))
    if summary.get("complete"):
        (EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS").write_text(
            "SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS\n"
        )
        return 0
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
