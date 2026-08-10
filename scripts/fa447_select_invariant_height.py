#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
from pathlib import Path

EXPECTED = [
    "champion",
    "height_only",
    "proof_invariant",
    "proof_invariant_height",
    "namespace_both",
    "namespace_both_height",
]
CHAMPION_SHA = "c12778aa72fa9541b064e466d59c854283766e73c02fda1a586cf7380e7f7626"
CHAMPION_INDEX = 2671
CHAMPION_POS = (32592, 5)
EXPECTED_LINES = 60453


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rank(metric: dict) -> tuple[int, int, int, int]:
    if int(metric["FA_exit"]) == 0:
        return (1, 10**9, 10**9, 10**9)
    return (
        0,
        int(metric.get("FA_error_declaration_index", -1)),
        int(metric.get("FA_first_actual_error_line", 0)),
        int(metric.get("FA_first_actual_error_col", 0)),
    )


def complete(metric: dict, source: Path) -> list[str]:
    reasons: list[str] = []
    if metric.get("classification") != "VERIFIED": reasons.append("metric_not_verified")
    if metric.get("all_required_lean_commands_executed") is not True: reasons.append("lean_not_executed")
    if sha(source) != metric.get("source_sha256"): reasons.append("source_sha_mismatch")
    if int(metric.get("line_count", 0)) != EXPECTED_LINES: reasons.append("line_count")
    if metric.get("same_height") is not True: reasons.append("not_same_height")
    if metric.get("theorem_header_unchanged") is not True: reasons.append("header_changed")
    if int(metric.get("Mock2_exit", 999)) != 0 or int(metric.get("Mock2_errors_under_cap", 999)) != 0:
        reasons.append("Mock2_not_clean")
    if int(metric.get("Mock2_Advanced_exit", 999)) != 0 or int(metric.get("Mock2_Advanced_errors_under_cap", 999)) != 0:
        reasons.append("Mock2_Advanced_not_clean")
    if metric.get("forbidden_clean") is not True: reasons.append("forbidden_audit")
    return reasons


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--collected", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    root = Path(args.collected)
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)

    rows: list[dict] = []
    loaded: dict[str, tuple[dict, Path]] = {}
    for variant in EXPECTED:
        d = root / variant
        metric_path = d / "METRIC.json"
        source = d / "Mock2_FunctionalAnalysis-candidate.lean"
        if not metric_path.exists() or not source.exists():
            raise RuntimeError(f"INFRA FAILURE: missing metric/source for {variant}")
        metric = json.loads(metric_path.read_text())
        if metric.get("variant") != variant:
            raise RuntimeError(f"INFRA FAILURE: variant mismatch for {variant}")
        reasons = complete(metric, source)
        if reasons:
            raise RuntimeError(f"INFRA FAILURE: incomplete direct metric {variant}: {reasons}")
        loaded[variant] = (metric, source)
        rows.append({
            "variant": variant,
            "source_sha256": metric["source_sha256"],
            "Lean_executed": True,
            "Mock2_exit": metric["Mock2_exit"],
            "Mock2_Advanced_exit": metric["Mock2_Advanced_exit"],
            "FA_exit": metric["FA_exit"],
            "first_line": metric["FA_first_actual_error_line"],
            "first_col": metric["FA_first_actual_error_col"],
            "declaration": metric["FA_first_error_declaration"],
            "declaration_index": metric["FA_error_declaration_index"],
        })

    champion, champion_source = loaded["champion"]
    if champion["source_sha256"] != CHAMPION_SHA or sha(champion_source) != CHAMPION_SHA:
        raise RuntimeError("INFRA FAILURE: current-run champion source identity mismatch")
    if int(champion["FA_exit"]) == 0:
        champion_rank = rank(champion)
    else:
        actual = (
            int(champion["FA_error_declaration_index"]),
            int(champion["FA_first_actual_error_line"]),
            int(champion["FA_first_actual_error_col"]),
        )
        if actual != (CHAMPION_INDEX, *CHAMPION_POS):
            raise RuntimeError(f"INFRA FAILURE: champion direct metric mismatch: {actual}")
        champion_rank = rank(champion)

    best_variant = max(EXPECTED, key=lambda v: rank(loaded[v][0]))
    best, best_source = loaded[best_variant]
    strict = rank(best) > champion_rank
    if int(best["FA_exit"]) == 0:
        classification = "FA_PASS_CANDIDATE"
    elif strict and int(best["FA_error_declaration_index"]) > CHAMPION_INDEX:
        classification = "DECLARATION_BREAKTHROUGH"
    elif strict:
        classification = "SMALL_SAME_DECLARATION_ADVANCE"
    else:
        classification = "NO_IMPROVEMENT"

    selection = {
        "classification": classification,
        "strict_promotion": strict,
        "authority": "complete current-run direct Lean CLI matrix",
        "champion": champion,
        "best": best,
        "candidate_results": rows,
    }
    (out / "SELECTION.json").write_text(json.dumps(selection, indent=2) + "\n")
    (out / "CANDIDATE_RESULTS.json").write_text(json.dumps(rows, indent=2) + "\n")
    shutil.copy2(best_source, out / "Mock2_FunctionalAnalysis-selected.lean")
    shutil.copy2(root / best_variant / "METRIC.json", out / "CHOSEN_METRIC.json")
    print(json.dumps(selection, indent=2))
    with open(os.environ["GITHUB_OUTPUT"], "a") as f:
        f.write(f"strict={str(strict).lower()}\n")
        f.write(f"variant={best_variant}\n")
        f.write(f"source_sha256={best['source_sha256']}\n")
        f.write(f"fa_exit={best['FA_exit']}\n")
        f.write(f"first_line={best['FA_first_actual_error_line']}\n")
        f.write(f"first_col={best['FA_first_actual_error_col']}\n")
        f.write(f"declaration={best['FA_first_error_declaration']}\n")
        f.write(f"classification={classification}\n")


if __name__ == "__main__":
    main()
