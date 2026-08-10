from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import Any

from fa442_pipeline_common import BASELINE_LINE_COUNT, BASELINE_SHA256, BLOCKER, REPO, read_json, write_json

ROOT = Path(os.environ.get(
    "REPORT_INPUT_ROOT",
    REPO / "build-logs/fa442-pipeline-repair/final-download",
))
OUT = REPO / "build-logs/fa442-pipeline-repair/final-report"


def find_one(name: str) -> Path | None:
    matches = list(ROOT.rglob(name))
    return matches[0] if matches else None


def load(name: str, default: Any = None) -> Any:
    path = find_one(name)
    return read_json(path) if path else default


def val(value: Any, default: Any = "") -> Any:
    return default if value is None else value


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    root_cause = load("ROOT_CAUSE.json", {})
    selection = load("selection.json", {})
    verification = load("verification.json", {})
    downstream = load("downstream.json", {
        "Integrated": "NOT_RUN_FA_NOT_TRUE_PASS",
        "Mock3_bridges": "NOT_RUN_FA_NOT_TRUE_PASS",
        "QYM": "NOT_RUN_FA_NOT_TRUE_PASS",
    })
    baseline = selection.get("baseline", {})
    selected = selection.get("selected", {})
    candidate_rows = selection.get("candidate_results", [])

    fa_true_pass = bool(verification.get("FA_TRUE_PASS"))
    if fa_true_pass:
        final_classification = "TRUE PASS"
    elif selection.get("classification") == "STRICT_PROMOTION":
        final_classification = "STRICT PROMOTION"
    elif selection.get("classification") == "NO_IMPROVEMENT":
        final_classification = "NO IMPROVEMENT"
    elif selection.get("classification") == "FA_PASS_CANDIDATE":
        final_classification = "STRICT PROMOTION"
    else:
        final_classification = "INFRA FAILURE"

    table_header = (
        "variant | SHA256 | Lean executed? | exit | first line:col | declaration | classification\n"
        "--- | --- | --- | --- | --- | --- | ---\n"
    )
    table_rows = []
    for row in candidate_rows:
        table_rows.append(
            f"{val(row.get('variant'))} | `{val(row.get('sha256'))}` | "
            f"{str(bool(row.get('lean_executed'))).lower()} | {val(row.get('exit'))} | "
            f"{val(row.get('first_line'), 0)}:{val(row.get('first_col'), 0)} | "
            f"`{val(row.get('declaration'))}` | {val(row.get('classification'))}"
        )
    table = table_header + "\n".join(table_rows)

    first_baseline = baseline.get("first_error", {})
    first_selected = selected.get("first_error", {})
    audit = verification.get("trust_audit", selected.get("trust_audit", {}))
    run1 = verification.get("FA_checked_in_run1", {})
    run2 = verification.get("FA_checked_in_run2", {})
    artifact_id = os.environ.get("FINAL_ARTIFACT_ID", "")
    branch = os.environ.get("REPAIR_BRANCH", "fix/fa442-matrix-direct-compile-repair-20260810")
    run_url = (
        f"https://github.com/{os.environ.get('GITHUB_REPOSITORY', 'leegahuyn/mathlib4')}"
        f"/actions/runs/{os.environ.get('GITHUB_RUN_ID', '')}"
    )
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=REPO,
        stdout=subprocess.PIPE, text=True, check=False,
    ).stdout.strip()

    markdown = f"""# FA MATRIX PIPELINE REPAIR REPORT

## Baseline

source SHA256: `{baseline.get('source_sha256', BASELINE_SHA256)}`

line count: `{baseline.get('line_count', BASELINE_LINE_COUNT)}`

direct Lean exit: `{baseline.get('direct_lean_exit', '')}`

first error: `{first_baseline.get('line', 0)}:{first_baseline.get('column', 0)}`

declaration: `{first_baseline.get('declaration', BLOCKER)}`

## Pipeline issue found

root cause: {root_cause.get('root_cause', 'No recoverable root-cause record; classified INFRA FAILURE.')}

workflow files changed:
- `.github/workflows/fa442-direct-matrix-pipeline-repair.yml`

scripts changed:
- `scripts/fa442_pipeline_common.py`
- `scripts/fa442_pipeline_prepare.py`
- `scripts/fa442_pipeline_metric.py`
- `scripts/fa442_pipeline_select.py`
- `scripts/fa442_pipeline_verify_checked_in.py`
- `scripts/fa442_pipeline_report.py`

## Candidate results

{table}

## Best direct-verified candidate

variant: `{selected.get('variant', '')}`

SHA256: `{selected.get('source_sha256', '')}`

exit: `{selected.get('exit', '')}`

first error: `{first_selected.get('line', 0)}:{first_selected.get('column', 0)}`

declaration: `{first_selected.get('declaration', '')}`

strictly better than 31726?: `{str(bool(selection.get('strictly_better'))).lower()}`

## Checked-in identity

selected SHA: `{verification.get('selected_sha256', selected.get('source_sha256', ''))}`

worktree SHA: `{verification.get('worktree_sha256', selected.get('worktree_sha256', ''))}`

HEAD source SHA: `{verification.get('HEAD_source_sha256', '')}`

identity_ok: `{str(bool(verification.get('identity_ok', selected.get('identity_ok_before_commit', False)))).lower()}`

## Trust audit

sorry: `{audit.get('sorry', '')}`

admit: `{audit.get('admit', '')}`

global axiom: `{audit.get('global_axiom', '')}`

unsafe: `{audit.get('unsafe', '')}`

native_decide: `{audit.get('native_decide', '')}`

Lean.ofReduceBool: `{audit.get('Lean.ofReduceBool', '')}`

## FA checked-in verification

run1: exit `{run1.get('exit_code', 'NOT_RUN')}`, errors `{run1.get('error_header_count', 'NOT_RUN')}`, olean `{run1.get('olean_exists', False)}`, ilean `{run1.get('ilean_exists', False)}`

run2: exit `{run2.get('exit_code', 'NOT_RUN')}`, errors `{run2.get('error_header_count', 'NOT_RUN')}`, olean `{run2.get('olean_exists', False)}`, ilean `{run2.get('ilean_exists', False)}`

FA_TRUE_PASS: `{str(fa_true_pass).lower()}`

## Downstream

Integrated: `{downstream.get('Integrated', 'NOT_RUN')}`

Mock3 bridges: `{downstream.get('Mock3_bridges', 'NOT_RUN')}`

QYM: `{downstream.get('QYM', 'NOT_RUN')}`

## Final classification

**{final_classification}**

## Branches/commits

branch: `{branch}`

report commit/worktree HEAD: `{head}`

Workflow run URL: {run_url}

Artifact ID: `{artifact_id}`
"""
    (OUT / "FA_MATRIX_PIPELINE_REPAIR_REPORT.md").write_text(markdown, encoding="utf-8")
    report = {
        "title": "FA MATRIX PIPELINE REPAIR REPORT",
        "baseline": baseline,
        "pipeline_issue_found": root_cause,
        "candidate_results": candidate_rows,
        "best_direct_verified_candidate": selected,
        "checked_in_identity": {
            "selected_sha": verification.get("selected_sha256", selected.get("source_sha256", "")),
            "worktree_sha": verification.get("worktree_sha256", selected.get("worktree_sha256", "")),
            "HEAD_source_sha": verification.get("HEAD_source_sha256", ""),
            "identity_ok": verification.get("identity_ok", selected.get("identity_ok_before_commit", False)),
        },
        "trust_audit": audit,
        "FA_checked_in_verification": verification,
        "downstream": downstream,
        "final_classification": final_classification,
        "branch": branch,
        "head": head,
        "workflow_run_url": run_url,
        "artifact_id": artifact_id,
    }
    write_json(OUT / "FA_MATRIX_PIPELINE_REPAIR_REPORT.json", report)
    print(markdown)


if __name__ == "__main__":
    main()
