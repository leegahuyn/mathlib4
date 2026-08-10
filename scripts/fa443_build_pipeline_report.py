#!/usr/bin/env python3
from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
BASE = ROOT / "build-logs/fa443-matrix"
SELECTED = BASE / "selected"
FINAL = BASE / "final-gates"


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else {}
    except Exception:
        return {}


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace").strip() if path.exists() else ""


def env_bool(name: str) -> bool:
    return os.environ.get(name, "false").lower() == "true"


def write_output(key: str, value: object) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a", encoding="utf-8") as handle:
            handle.write(f"{key}={value}\n")


selection = load_json(SELECTED / "SELECTION.json")
confirmation = load_json(SELECTED / "CONFIRMATION.json")
fa_final = load_json(FINAL / "FA_FINAL.json")
downstream = load_json(FINAL / "DOWNSTREAM.json")
identity = load_json(FINAL / "CHECKED_IN_IDENTITY.json")
candidate_results = load_json(SELECTED / "CANDIDATE_RESULTS.json")
if not candidate_results:
    try:
        value = json.loads((SELECTED / "CANDIDATE_RESULTS.json").read_text(encoding="utf-8"))
        candidate_results_value: Any = value if isinstance(value, list) else []
    except Exception:
        candidate_results_value = []
else:
    candidate_results_value = candidate_results

selector_ok = env_bool("SELECTOR_OK") and bool(selection)
confirmation_ok = confirmation.get("verified") is True
identity_ok = identity.get("identity_ok") is True
fa_true_pass = fa_final.get("FA_TRUE_PASS") is True
selection_mode = str(selection.get("selection_mode", ""))
selection_classification = str(selection.get("classification", ""))

pipeline_infra_reasons: list[str] = []
if not selector_ok:
    pipeline_infra_reasons.append("selector did not complete with a full current-run direct matrix")
if not confirmation_ok:
    pipeline_infra_reasons.append("independent selected-source direct confirmation failed")
if not identity_ok:
    pipeline_infra_reasons.append("selected/worktree/HEAD checked-in source identity failed")
if not fa_final:
    pipeline_infra_reasons.append("checked-in FA two-pass gate evidence missing")

pipeline_ok = not pipeline_infra_reasons
if not pipeline_ok:
    final_classification = "INFRA FAILURE"
elif fa_true_pass:
    final_classification = "TRUE PASS"
elif selection_mode == "strict_promotion":
    final_classification = "STRICT PROMOTION"
else:
    final_classification = "NO IMPROVEMENT"

report = {
    "title": "FA MATRIX PIPELINE REPAIR REPORT",
    "workflow_run_id": os.environ.get("GITHUB_RUN_ID", ""),
    "workflow_run_url": (
        f"https://github.com/{os.environ.get('GITHUB_REPOSITORY', 'leegahuyn/mathlib4')}"
        f"/actions/runs/{os.environ.get('GITHUB_RUN_ID', '')}"
    ),
    "trigger_sha": os.environ.get("GITHUB_SHA", ""),
    "pipeline_ok": pipeline_ok,
    "pipeline_infra_reasons": pipeline_infra_reasons,
    "baseline": selection.get("baseline", {}),
    "candidate_results": candidate_results_value,
    "best_direct_verified_candidate": selection.get("chosen", {}),
    "selection_mode": selection_mode,
    "selection_classification": selection_classification,
    "independent_confirmation": confirmation,
    "checked_in_identity": identity,
    "trust_audit": confirmation.get("forbidden_audit", {}),
    "FA_checked_in_verification": fa_final,
    "downstream": downstream,
    "FA_TRUE_PASS": fa_true_pass,
    "final_classification": final_classification,
    "maxErrors_policy": "caps are diagnostic only and are not interpreted as total errors or progress",
}
BASE.mkdir(parents=True, exist_ok=True)
(BASE / "PIPELINE_REPORT.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)

chosen = report["best_direct_verified_candidate"] if isinstance(report["best_direct_verified_candidate"], dict) else {}
baseline = report["baseline"] if isinstance(report["baseline"], dict) else {}
lines = [
    "FA MATRIX PIPELINE REPAIR REPORT",
    "",
    "Baseline:",
    f"source SHA256: {baseline.get('source_sha256', '')}",
    f"line count: {baseline.get('line_count', '')}",
    f"direct Lean exit: {baseline.get('FA_exit', '')}",
    f"first error: {baseline.get('FA_first_actual_error_line', '')}:{baseline.get('FA_first_actual_error_col', '')}",
    f"declaration: {baseline.get('FA_first_error_declaration', '')}",
    "",
    "Pipeline issue found:",
    "root cause: mutable branch checkout changed the checked-in source before candidate preparation; prepare.ok=false then skipped Lean install and compile; selector received no baseline direct metric; git identity existed only in a skipped step.",
    "workflow files changed: .github/workflows/fa443-matrix-direct-repair.yml",
    "scripts changed: scripts/fa443_record_direct_metric.py, scripts/fa443_select_direct_champion.py, scripts/fa443_confirm_selected.py, scripts/fa443_checked_in_fa_gate.py, scripts/fa443_build_pipeline_report.py",
    "",
    "Best direct-verified candidate:",
    f"variant: {chosen.get('variant', '')}",
    f"SHA256: {chosen.get('source_sha256', '')}",
    f"exit: {chosen.get('FA_exit', '')}",
    f"first error: {chosen.get('FA_first_actual_error_line', '')}:{chosen.get('FA_first_actual_error_col', '')}",
    f"declaration: {chosen.get('FA_first_error_declaration', '')}",
    f"strictly better than 31726?: {selection_mode == 'strict_promotion'}",
    "",
    "Checked-in identity:",
    f"selected SHA: {identity.get('selected_sha256', '')}",
    f"worktree SHA: {identity.get('worktree_sha256', '')}",
    f"HEAD source SHA: {identity.get('head_source_sha256', '')}",
    f"identity_ok: {identity.get('identity_ok', False)}",
    "",
    "FA checked-in verification:",
    f"run1: {(fa_final.get('runs') or [{}])[0] if fa_final.get('runs') else {}}",
    f"run2: {(fa_final.get('runs') or [{}, {}])[1] if len(fa_final.get('runs') or []) > 1 else {}}",
    f"FA_TRUE_PASS: {fa_true_pass}",
    "",
    "Downstream:",
    f"Integrated: {downstream.get('Integrated', 'BLOCKED')}",
    f"Mock3 bridges: {downstream.get('Mock3_bridges', 'BLOCKED')}",
    f"QYM: {downstream.get('QYM', 'BLOCKED')}",
    "",
    f"Final classification: {final_classification}",
    f"Workflow run URL: {report['workflow_run_url']}",
]
(BASE / "PIPELINE_REPORT.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
print(json.dumps(report, indent=2))
write_output("pipeline_ok", str(pipeline_ok).lower())
write_output("fa_true_pass", str(fa_true_pass).lower())
write_output("final_classification", final_classification)
