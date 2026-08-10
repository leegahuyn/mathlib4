#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import os
import re
import shutil
import subprocess
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
SRC = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
BASELINE = Path("/tmp/fa426-baseline.lean")
SELECTION = Path("/tmp/fa426-selection.json")
REFS = Path("/tmp/fa425-donor-refs.txt")
LOG_DIR = ROOT / "build-logs/fa426-multiround-cross-donor"
ROUND_ROOT = LOG_DIR / "rounds"

spec = importlib.util.spec_from_file_location("fa425_common", ROOT / "scripts/fa425_run_strict_controller.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot import FA425 common direct compiler")
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)
common.LOG_DIR = LOG_DIR
common.CANDIDATES = LOG_DIR / "unused-candidates"


def emit(values: dict[str, str]) -> None:
    out = os.environ.get("GITHUB_OUTPUT")
    if not out:
        return
    with open(out, "a", encoding="utf-8") as f:
        for k, v in values.items():
            f.write(f"{k}={v}\n")


def direct_metric_not_worse(metric: Any, evidence: dict[str, Any]) -> bool:
    selected = evidence.get("selected", {})
    recorded = selected.get("metric", {})
    if recorded.get("exit_zero"):
        return common.passed(metric)
    required = int(recorded.get("first_error_line", 0))
    return metric.first_error_line >= required and metric.first_error_line > 0


def main() -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    ROUND_ROOT.mkdir(parents=True, exist_ok=True)
    if not BASELINE.exists() or not SELECTION.exists():
        raise SystemExit("FA426 selected baseline or metadata missing")
    selection = json.loads(SELECTION.read_text(encoding="utf-8"))
    original_sha = common.sha(SRC)
    shutil.copy2(BASELINE, SRC)

    m2 = common.compile_source("Mock2", "Mock2-prerequisite", 400)
    m2a = common.compile_source("Mock2_Advanced", "Mock2_Advanced-prerequisite", 400)
    baseline = common.compile_source("Mock2_FunctionalAnalysis", "FA-baseline-direct", 1) if common.passed(m2) and common.passed(m2a) else None
    baseline_verified = bool(
        baseline is not None and common.passed(m2) and common.passed(m2a) and
        baseline.line_count == 60453 and direct_metric_not_worse(baseline, selection)
    )
    status: dict[str, Any] = {
        "classification": "VERIFIED" if baseline_verified else "INFRA FAILURE",
        "stage": "baseline direct reverify",
        "selection": selection,
        "original_branch_source_sha256": original_sha,
        "Mock2": asdict(m2),
        "Mock2_Advanced": asdict(m2a),
        "baseline": asdict(baseline) if baseline else None,
        "baseline_verified": baseline_verified,
        "rounds": [],
        "strict_promotion": False,
        "fa_true_pass": False,
        "all_required_targets_2x_pass": False,
    }
    if baseline is not None:
        common.write_context(baseline, SRC, LOG_DIR / "BASELINE_FIRST_ERROR_CONTEXT.txt")

    if not baseline_verified or baseline is None:
        shutil.copy2(BASELINE, SRC)
        (LOG_DIR / "INFRA_FAILURE").touch()
        (LOG_DIR / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
        emit({"source_should_commit": "false", "strict_promotion": "false", "fa_true_pass": "false", "all_chain_pass": "false", "controller_success": "false"})
        return

    current_metric = baseline
    current_source = BASELINE
    promoted_any = False

    for round_no in range(1, 5):
        if common.passed(current_metric):
            break
        round_dir = ROUND_ROOT / f"round-{round_no}"
        candidate_dir = round_dir / "candidates"
        round_dir.mkdir(parents=True, exist_ok=True)
        round_baseline = round_dir / "baseline.lean"
        shutil.copy2(current_source, round_baseline)
        subprocess.run([
            "python3", "scripts/fa426_dynamic_hunk_candidates.py",
            "--baseline", str(round_baseline),
            "--output", str(candidate_dir),
            "--refs", str(REFS),
            "--first-error-line", str(current_metric.first_error_line),
            "--limit", "12",
        ], check=True)
        manifest = json.loads((candidate_dir / "MANIFEST.json").read_text(encoding="utf-8"))
        rows = []
        best = None
        for idx, item in enumerate(manifest.get("candidates", [])):
            path = candidate_dir / item["file"]
            shutil.copy2(path, SRC)
            label = f"round{round_no}-candidate{idx:02d}-{re.sub(r'[^A-Za-z0-9_.-]+', '-', item['name'])[:70]}"
            metric = common.compile_source("Mock2_FunctionalAnalysis", label, 1)
            better = common.strictly_better(metric, current_metric)
            row = {"candidate": item, "metric": asdict(metric), "strictly_better": better}
            rows.append(row)
            if better and (best is None or common.metric_rank(metric) > common.metric_rank(best[0])):
                best = (metric, path, item)
        round_record: dict[str, Any] = {
            "round": round_no,
            "baseline": asdict(current_metric),
            "generator": manifest,
            "rows": rows,
            "promotion": None,
        }
        if best is None:
            round_record["result"] = "no strict improvement"
            status["rounds"].append(round_record)
            (round_dir / "ROUND.json").write_text(json.dumps(round_record, indent=2) + "\n", encoding="utf-8")
            break

        screen, best_path, best_item = best
        shutil.copy2(best_path, SRC)
        verify1 = common.compile_source("Mock2_FunctionalAnalysis", f"round{round_no}-promotion-reverify1", 1)
        verify2 = common.compile_source("Mock2_FunctionalAnalysis", f"round{round_no}-promotion-reverify2", 1)
        consistent = (
            verify1.source_sha256 == verify2.source_sha256 == best_item["sha256"] and
            verify1.line_count == verify2.line_count == current_metric.line_count and
            common.strictly_better(verify1, current_metric) and common.strictly_better(verify2, current_metric) and
            common.metric_rank(verify1) == common.metric_rank(verify2)
        )
        promotion = {
            "candidate": best_item,
            "screen": asdict(screen),
            "reverify_run1": asdict(verify1),
            "reverify_run2": asdict(verify2),
            "consistent": consistent,
        }
        round_record["promotion"] = promotion
        if not consistent:
            round_record["result"] = "promotion rejected by direct reverify"
            status["rounds"].append(round_record)
            (round_dir / "ROUND.json").write_text(json.dumps(round_record, indent=2) + "\n", encoding="utf-8")
            shutil.copy2(current_source, SRC)
            break

        promoted_any = True
        round_record["result"] = "strict promotion"
        status["rounds"].append(round_record)
        (round_dir / "ROUND.json").write_text(json.dumps(round_record, indent=2) + "\n", encoding="utf-8")
        current_metric = verify2
        current_source = round_dir / "promoted.lean"
        shutil.copy2(best_path, current_source)
        common.write_context(verify2, SRC, round_dir / "PROMOTED_FIRST_ERROR_CONTEXT.txt")

    shutil.copy2(current_source, SRC)
    status["strict_promotion"] = promoted_any
    status["selected_metric"] = asdict(current_metric)
    status["selected_source_sha256"] = common.sha(SRC)
    status["selected_line_count"] = common.line_count(SRC)

    if common.passed(current_metric):
        fa1 = common.compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run1", 2000)
        fa2 = common.compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run2", 2000)
        audit = common.trust_audit(SRC)
        fa_true_pass = common.passed(fa1) and common.passed(fa2) and fa1.source_sha256 == fa2.source_sha256 == common.sha(SRC) and audit["clean"]
        status["FA_final_run1"] = asdict(fa1)
        status["FA_final_run2"] = asdict(fa2)
        status["trust_audit"] = audit
        status["fa_true_pass"] = fa_true_pass
        if fa_true_pass:
            (LOG_DIR / "FA_TRUE_PASS_2X_AUDIT_CLEAN").touch()
            downstream = common.run_ordered_downstream()
            status["downstream"] = downstream
            status["all_required_targets_2x_pass"] = bool(downstream.get("complete"))
            if status["all_required_targets_2x_pass"]:
                (LOG_DIR / "ALL_REQUIRED_TARGETS_2X_PASS").touch()

    materialize_baseline = original_sha != common.sha(BASELINE)
    source_should_commit = bool(promoted_any or materialize_baseline or status["fa_true_pass"])
    status["materialize_verified_baseline"] = materialize_baseline and not promoted_any
    status["source_should_commit"] = source_should_commit
    status["stage"] = (
        "all ordered targets 2x pass" if status["all_required_targets_2x_pass"] else
        "FA true pass" if status["fa_true_pass"] else
        "multiround strict frontier promoted" if promoted_any else
        "verified baseline materialized" if materialize_baseline else
        "no strict promotion"
    )
    (LOG_DIR / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    (LOG_DIR / "CURRENT.txt").write_text(
        f"classification={status['classification']}\n"
        f"stage={status['stage']}\n"
        f"selected_source_sha256={status['selected_source_sha256']}\n"
        f"selected_line_count={status['selected_line_count']}\n"
        f"FA_exit={current_metric.exit_code}\n"
        f"FA_first_error={current_metric.first_error_line}:{current_metric.first_error_col}\n"
        f"FA_declaration={current_metric.first_error_declaration}\n"
        f"strict_promotion={str(promoted_any).lower()}\n"
        f"fa_true_pass={str(status['fa_true_pass']).lower()}\n"
        f"all_required_targets_2x_pass={str(status['all_required_targets_2x_pass']).lower()}\n",
        encoding="utf-8",
    )
    emit({
        "source_should_commit": str(source_should_commit).lower(),
        "strict_promotion": str(promoted_any).lower(),
        "fa_true_pass": str(status["fa_true_pass"]).lower(),
        "all_chain_pass": str(status["all_required_targets_2x_pass"]).lower(),
        "controller_success": str(bool(promoted_any or materialize_baseline or status["fa_true_pass"])).lower(),
    })


if __name__ == "__main__":
    main()
