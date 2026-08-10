#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import os
import shutil
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
SELECTED = Path("/tmp/fa432-selected.lean")
SELECTION = Path("/tmp/fa432-selection.json")
LOG_DIR = ROOT / "build-logs/fa432-authoritative-best-reverify"

spec = importlib.util.spec_from_file_location("fa432_common", ROOT / "scripts/fa425_run_strict_controller.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load direct compiler helper")
common = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = common
spec.loader.exec_module(common)
common.LOG_DIR = LOG_DIR


def score(metric: Any) -> tuple[int, int, int]:
    return (1 if common.passed(metric) else 0, int(metric.first_error_line), int(metric.first_error_col))


def selected_score(metadata: dict[str, Any]) -> tuple[int, int, int]:
    selected = metadata.get("selected", {})
    raw = selected.get("score")
    if isinstance(raw, list) and len(raw) >= 3:
        return tuple(int(value) for value in raw[:3])
    metric = selected.get("metric", {})
    return (
        1 if metric.get("exit_zero") else 0,
        int(metric.get("first_error_line", 0)),
        int(metric.get("first_error_col", 0)),
    )


def emit(values: dict[str, str]) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if not output:
        return
    with open(output, "a", encoding="utf-8") as file:
        for key, value in values.items():
            file.write(f"{key}={value}\n")


def main() -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    if not SELECTED.exists() or not SELECTION.exists():
        raise SystemExit("selected source or metadata missing")
    metadata = json.loads(SELECTION.read_text(encoding="utf-8"))
    original_sha = common.sha(SOURCE)
    shutil.copy2(SELECTED, SOURCE)
    selected_sha = common.sha(SOURCE)
    selected_lines = common.line_count(SOURCE)
    if selected_lines != 60453:
        raise SystemExit(f"selected source line count {selected_lines} != 60453")

    m2 = common.compile_source("Mock2", "Mock2-direct", 500)
    m2a = common.compile_source("Mock2_Advanced", "Mock2_Advanced-direct", 500)
    status: dict[str, Any] = {
        "classification": "INFRA FAILURE",
        "authority": "fresh direct Lean CLI on the selected checked-in source",
        "selection": metadata,
        "original_branch_source_sha256": original_sha,
        "selected_source_sha256": selected_sha,
        "selected_line_count": selected_lines,
        "Mock2": asdict(m2),
        "Mock2_Advanced": asdict(m2a),
        "FA_reverify_run1": None,
        "FA_reverify_run2": None,
        "verified": False,
        "fa_true_pass": False,
        "all_required_targets_2x_pass": False,
    }
    if not common.passed(m2) or not common.passed(m2a):
        status["blocked"] = "Mock2 prerequisite regression"
    else:
        first = common.compile_source("Mock2_FunctionalAnalysis", "FA-reverify-run1", 1)
        second = common.compile_source("Mock2_FunctionalAnalysis", "FA-reverify-run2", 1)
        status["FA_reverify_run1"] = asdict(first)
        status["FA_reverify_run2"] = asdict(second)
        consistent = (
            first.source_sha256 == second.source_sha256 == selected_sha and
            first.line_count == second.line_count == selected_lines and
            score(first) == score(second)
        )
        not_regressed = score(second) >= selected_score(metadata)
        verified = consistent and not_regressed
        status["consistent"] = consistent
        status["not_regressed_below_selection"] = not_regressed
        status["verified"] = verified
        status["classification"] = "VERIFIED" if verified else "INFRA FAILURE"
        common.write_context(second, SOURCE, LOG_DIR / "FIRST_ERROR_CONTEXT.txt")

        if verified and common.passed(second):
            fa1 = common.compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run1", 3000)
            fa2 = common.compile_source("Mock2_FunctionalAnalysis", "FA-final-direct-run2", 3000)
            audit = common.trust_audit(SOURCE)
            fa_true_pass = (
                common.passed(fa1) and common.passed(fa2) and
                fa1.source_sha256 == fa2.source_sha256 == selected_sha and audit["clean"]
            )
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

    materialize = status.get("verified") is True and original_sha != selected_sha
    status["source_should_commit"] = materialize or status["fa_true_pass"]
    status["stage"] = (
        "FA Integrated Mock3 QYM ordered x2 PASS" if status["all_required_targets_2x_pass"] else
        "Mock2_FunctionalAnalysis TRUE PASS x2 and trust audit clean" if status["fa_true_pass"] else
        "authoritative frontier reverified" if status.get("verified") else
        "authoritative reverify failed"
    )
    (LOG_DIR / "CURRENT.json").write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    second = status.get("FA_reverify_run2") or {}
    (LOG_DIR / "CURRENT.txt").write_text(
        f"classification={status['classification']}\n"
        f"stage={status['stage']}\n"
        f"source_sha256={selected_sha}\n"
        f"line_count={selected_lines}\n"
        f"FA_exit={second.get('exit_code', '')}\n"
        f"FA_first_error={second.get('first_error_line', '')}:{second.get('first_error_col', '')}\n"
        f"FA_declaration={second.get('first_error_declaration', '')}\n"
        f"verified={str(status.get('verified', False)).lower()}\n"
        f"fa_true_pass={str(status['fa_true_pass']).lower()}\n"
        f"all_required_targets_2x_pass={str(status['all_required_targets_2x_pass']).lower()}\n",
        encoding="utf-8",
    )
    emit({
        "verified": str(bool(status.get("verified"))).lower(),
        "source_should_commit": str(bool(status["source_should_commit"])).lower(),
        "fa_true_pass": str(bool(status["fa_true_pass"])).lower(),
        "all_chain_pass": str(bool(status["all_required_targets_2x_pass"])).lower(),
        "source_sha256": selected_sha,
        "first_error_line": str(second.get("first_error_line", "")),
        "first_error_col": str(second.get("first_error_col", "")),
        "declaration": str(second.get("first_error_declaration", "")),
    })
    print(json.dumps(status, indent=2))


if __name__ == "__main__":
    main()
