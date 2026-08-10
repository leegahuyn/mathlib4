from __future__ import annotations

import json
import shutil
import sys
from pathlib import Path

from fa442_pipeline_common import FA442_RUN_ID, REPO, write_json
from fa442_pipeline_prepare import REPOSITORY, api_json, diagnose, paged, workflow_from_run

OUT = REPO / "build-logs/fa442-skip-root-cause"


def main() -> None:
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True)
    run = api_json(f"/repos/{REPOSITORY}/actions/runs/{FA442_RUN_ID}")
    jobs = paged(f"/repos/{REPOSITORY}/actions/runs/{FA442_RUN_ID}/jobs", "jobs")
    workflow_path, workflow = workflow_from_run(run)
    root = diagnose(run, jobs, workflow_path, workflow)
    write_json(OUT / "RUN.json", run)
    write_json(OUT / "JOBS.json", {"jobs": jobs})
    write_json(OUT / "ROOT_CAUSE.json", root)
    (OUT / "WORKFLOW.yml").write_text(workflow, encoding="utf-8")
    lines = [
        "# FA442 SKIP ROOT CAUSE",
        "",
        f"Run: {root.get('run_url', '')}",
        "",
        f"Workflow path: `{root.get('workflow_path', '')}`",
        "",
        "## Verified root cause",
        "",
        root.get("root_cause", ""),
        "",
        "## Skipped direct-compile path",
        "",
    ]
    for row in root.get("skipped_steps", []):
        lines.extend([
            f"- job `{row.get('job_name')}` / step `{row.get('step_name')}`",
            f"  - conclusion: `{row.get('conclusion')}`",
            f"  - actual condition: `{row.get('condition') or '<none>'}`",
        ])
        for ref in row.get("output_references", []):
            lines.append(
                f"  - output `{ref.get('reference')}`: owner_exists={ref.get('owner_exists')}, "
                f"definition_found={ref.get('output_definition_found')}"
            )
    lines.extend([
        "",
        "## Selector failure",
        "",
        f"`{root.get('selector_failure', '')}`",
        "",
        "## Evidence commit failure",
        "",
        f"`{root.get('git_identity_failure', '')}`",
        "",
        "## Repair invariant",
        "",
        "The replacement matrix and sequential fallback run Lean setup and direct compile without "
        "candidate-metadata output guards. A nonexecuted direct compile is emitted as "
        "`INFRA_FAILURE`, never as a successful candidate.",
        "",
    ])
    (OUT / "ROOT_CAUSE.md").write_text("\n".join(lines), encoding="utf-8")
    print(json.dumps(root, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        OUT.mkdir(parents=True, exist_ok=True)
        write_json(OUT / "INFRA_FAILURE.json", {
            "classification": "INFRA_FAILURE",
            "stage": "FA442 diagnose only",
            "error": repr(exc),
        })
        raise
