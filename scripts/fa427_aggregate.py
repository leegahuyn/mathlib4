#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import shutil
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
BUILD_LOGS = ROOT / "build-logs/fa427-parallel-frontier-loop"

spec = importlib.util.spec_from_file_location("fa427_aggregate_common", ROOT / "scripts/fa425_run_strict_controller.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load direct compiler helper")
common = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = common
spec.loader.exec_module(common)
common.LOG_DIR = BUILD_LOGS


def metric_from_dict(row: dict[str, Any]) -> Any:
    fields = {name for name in common.Metric.__dataclass_fields__}
    return common.Metric(**{k: row[k] for k in fields})


def screen_rank(metric: Any) -> tuple[int, int, int]:
    return (1 if common.passed(metric) else 0, int(metric.first_error_line), int(metric.first_error_col))


def strict(metric: Any, baseline: Any) -> bool:
    return common.strictly_better(metric, baseline)


def round_number() -> int:
    path = ROOT / "fa427-requests/REQUESTED.txt"
    if not path.exists():
        return 1
    m = re.search(r"(?m)^round=(\d+)\s*$", path.read_text(encoding="utf-8", errors="replace"))
    return int(m.group(1)) if m else 1


def emit(values: dict[str, str]) -> None:
    out = os.environ.get("GITHUB_OUTPUT")
    if not out:
        return
    with open(out, "a", encoding="utf-8") as f:
        for k, v in values.items():
            f.write(f"{k}={v}\n")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--prepared", required=True)
    ap.add_argument("--screens", required=True)
    args = ap.parse_args()

    prepared = Path(args.prepared)
    screens = Path(args.screens)
    BUILD_LOGS.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((prepared / "MANIFEST.json").read_text(encoding="utf-8"))
    baseline = metric_from_dict(manifest["baseline"])
    baseline_source = prepared / "baseline.lean"
    original_branch_sha = common.sha(SOURCE)
    if common.sha(baseline_source) != baseline.source_sha256 or common.line_count(baseline_source) != baseline.line_count:
        raise SystemExit("prepared baseline identity mismatch")

    screen_rows: list[dict[str, Any]] = []
    best: tuple[Any, Path, dict[str, Any]] | None = None
    for result_path in sorted(screens.rglob("RESULT.json")):
        try:
            result = json.loads(result_path.read_text(encoding="utf-8"))
            metric = metric_from_dict(result["metric"])
            source = result_path.parent / "candidate.lean"
        except Exception as exc:
            screen_rows.append({"path": str(result_path), "parse_error": str(exc)})
            continue
        identity_ok = (
            source.exists() and common.sha(source) == metric.source_sha256 == result["candidate"]["source_sha256"] and
            common.line_count(source) == metric.line_count == baseline.line_count
        )
        better = identity_ok and strict(metric, baseline)
        row = {
            "artifact_path": str(result_path),
            "candidate": result["candidate"],
            "metric": asdict(metric),
            "identity_ok": identity_ok,
            "strictly_better": better,
        }
        screen_rows.append(row)
        if better and (best is None or screen_rank(metric) > screen_rank(best[0])):
            best = (metric, source, result["candidate"])

    (BUILD_LOGS / "SCREENING_SUMMARY.json").write_text(json.dumps({
        "authority": "direct Lean CLI",
        "maxErrors_cap": 1,
        "maxErrors_interpretation": "candidate screening stops after first actual error; not total errors or proof percentage",
        "baseline": asdict(baseline),
        "rows": screen_rows,
    }, indent=2) + "\n", encoding="utf-8")

    # Aggregate authority: directly rebuild prerequisites and selected source in a
    # fresh job, then require two identical direct frontier measurements.
    m2 = common.compile_source("Mock2", "Mock2-aggregate-direct", 500)
    m2a = common.compile_source("Mock2_Advanced", "Mock2_Advanced-aggregate-direct", 500)
    if not common.passed(m2) or not common.passed(m2a):
        raise SystemExit("Mock2 prerequisite regression in aggregate job")

    selected_kind = "baseline"
    selected_candidate: dict[str, Any] | None = None
    selected_source = baseline_source
    if best is not None:
        selected_kind = "screen-winner"
        selected_source = best[1]
        selected_candidate = best[2]
    shutil.copy2(selected_source, SOURCE)
    verify1 = common.compile_source("Mock2_FunctionalAnalysis", "FA-selected-reverify-run1", 1)
    verify2 = common.compile_source("Mock2_FunctionalAnalysis", "FA-selected-reverify-run2", 1)
    identity = (
        verify1.source_sha256 == verify2.source_sha256 == common.sha(selected_source) and
        verify1.line_count == verify2.line_count == baseline.line_count and
        screen_rank(verify1) == screen_rank(verify2)
    )
    strict_promotion = selected_kind == "screen-winner" and identity and strict(verify1, baseline) and strict(verify2, baseline)

    if selected_kind == "screen-winner" and not strict_promotion:
        selected_kind = "baseline-after-reverify-rejection"
        selected_candidate = None
        selected_source = baseline_source
        shutil.copy2(baseline_source, SOURCE)
        verify1 = common.compile_source("Mock2_FunctionalAnalysis", "FA-baseline-fallback-reverify-run1", 1)
        verify2 = common.compile_source("Mock2_FunctionalAnalysis", "FA-baseline-fallback-reverify-run2", 1)
        identity = (
            verify1.source_sha256 == verify2.source_sha256 == baseline.source_sha256 and
            verify1.line_count == verify2.line_count == baseline.line_count and
            screen_rank(verify1) == screen_rank(verify2) and screen_rank(verify2) >= screen_rank(baseline)
        )
        if not identity:
            raise SystemExit("selected candidate rejected and baseline failed fresh aggregate reverify")

    common.write_context(verify2, SOURCE, BUILD_LOGS / "SELECTED_FIRST_ERROR_CONTEXT.txt")
    promotion_record = {
        "selected_kind": selected_kind,
        "candidate": selected_candidate,
        "baseline": asdict(baseline),
        "reverify_run1": asdict(verify1),
        "reverify_run2": asdict(verify2),
        "identity_consistent": identity,
        "strict_promotion": strict_promotion,
    }
    (BUILD_LOGS / "SELECTION_REVERIFY.json").write_text(json.dumps(promotion_record, indent=2) + "\n", encoding="utf-8")

    status: dict[str, Any] = {
        "classification": "VERIFIED",
        "round": round_number(),
        "stage": "strict frontier promoted" if strict_promotion else "verified baseline retained",
        "Mock2": asdict(m2),
        "Mock2_Advanced": asdict(m2a),
        "baseline": asdict(baseline),
        "selection": promotion_record,
        "strict_promotion": strict_promotion,
        "selected_source_sha256": common.sha(SOURCE),
        "selected_line_count": common.line_count(SOURCE),
        "selected_metric": asdict(verify2),
        "fa_true_pass": False,
        "all_required_targets_2x_pass": False,
    }

    if common.passed(verify2):
        fa1 = common.compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run1", 2500)
        fa2 = common.compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run2", 2500)
        audit = common.trust_audit(SOURCE)
        fa_true_pass = (
            common.passed(fa1) and common.passed(fa2) and
            fa1.source_sha256 == fa2.source_sha256 == common.sha(SOURCE) and audit["clean"]
        )
        status["FA_final_run1"] = asdict(fa1)
        status["FA_final_run2"] = asdict(fa2)
        status["trust_audit"] = audit
        status["fa_true_pass"] = fa_true_pass
        if fa_true_pass:
            status["stage"] = "Mock2_FunctionalAnalysis TRUE PASS x2 and trust audit clean"
            (BUILD_LOGS / "FA_TRUE_PASS_2X_AUDIT_CLEAN").touch()
            downstream = common.run_ordered_downstream()
            status["downstream"] = downstream
            status["all_required_targets_2x_pass"] = bool(downstream.get("complete"))
            if status["all_required_targets_2x_pass"]:
                status["stage"] = "FA Integrated Mock3 QYM ordered x2 PASS"
                (BUILD_LOGS / "ALL_REQUIRED_TARGETS_2X_PASS").touch()

    materialize_baseline = not strict_promotion and original_branch_sha != baseline.source_sha256
    source_should_commit = bool(strict_promotion or materialize_baseline or status["fa_true_pass"])
    current_round = status["round"]
    continue_loop = bool(strict_promotion and not status["fa_true_pass"] and current_round < 12)
    status["materialize_verified_baseline"] = materialize_baseline
    status["source_should_commit"] = source_should_commit
    status["continue_loop"] = continue_loop
    status["next_round"] = current_round + 1 if continue_loop else None
    (BUILD_LOGS / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    (BUILD_LOGS / "CURRENT.txt").write_text(
        f"classification=VERIFIED\n"
        f"round={current_round}\n"
        f"stage={status['stage']}\n"
        f"source_sha256={status['selected_source_sha256']}\n"
        f"line_count={status['selected_line_count']}\n"
        f"FA_exit={verify2.exit_code}\n"
        f"FA_first_error={verify2.first_error_line}:{verify2.first_error_col}\n"
        f"FA_declaration={verify2.first_error_declaration}\n"
        f"strict_promotion={str(strict_promotion).lower()}\n"
        f"fa_true_pass={str(status['fa_true_pass']).lower()}\n"
        f"all_required_targets_2x_pass={str(status['all_required_targets_2x_pass']).lower()}\n"
        f"continue_loop={str(continue_loop).lower()}\n",
        encoding="utf-8",
    )
    emit({
        "source_should_commit": str(source_should_commit).lower(),
        "strict_promotion": str(strict_promotion).lower(),
        "fa_true_pass": str(status["fa_true_pass"]).lower(),
        "all_chain_pass": str(status["all_required_targets_2x_pass"]).lower(),
        "continue_loop": str(continue_loop).lower(),
        "next_round": str(status["next_round"] or ""),
        "selected_sha256": status["selected_source_sha256"],
        "selected_first_error_line": str(verify2.first_error_line),
        "selected_first_error_col": str(verify2.first_error_col),
        "selected_declaration": verify2.first_error_declaration,
        "controller_success": str(bool(strict_promotion or materialize_baseline or status["fa_true_pass"])).lower(),
    })
    print(json.dumps(status, indent=2))


if __name__ == "__main__":
    main()
