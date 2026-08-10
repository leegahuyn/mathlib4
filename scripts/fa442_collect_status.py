from __future__ import annotations

import base64
import json
import os
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

REPOSITORY = os.environ.get("GITHUB_REPOSITORY", "leegahuyn/mathlib4")
TOKEN = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN", "")
API = "https://api.github.com"
OUT = Path("build-logs/fa442-status-dashboard")

TARGETS = [
    {
        "branch": "fix/fa442-skip-root-cause-20260810",
        "workflow_name": "FA442 exact skipped-step root cause",
        "report_paths": [
            "build-logs/fa442-skip-root-cause/ROOT_CAUSE.json",
            "build-logs/fa442-skip-root-cause/ROOT_CAUSE.md",
        ],
    },
    {
        "branch": "fix/fa442-matrix-direct-compile-repair-20260810",
        "workflow_name": "FA442 direct matrix pipeline repair",
        "report_paths": [
            "build-logs/fa442-pipeline-repair/final-report/FA_MATRIX_PIPELINE_REPAIR_REPORT.json",
            "build-logs/fa442-pipeline-repair/final-report/FA_MATRIX_PIPELINE_REPAIR_REPORT.md",
            "build-logs/fa442-pipeline-repair/selection/selection.json",
        ],
    },
    {
        "branch": "fix/fa442-sequential-direct-tournament-20260810",
        "workflow_name": "FA442 sequential direct tournament recovery",
        "report_paths": [
            "build-logs/fa442-pipeline-repair/final-report/FA_MATRIX_PIPELINE_REPAIR_REPORT.json",
            "build-logs/fa442-pipeline-repair/final-report/FA_MATRIX_PIPELINE_REPAIR_REPORT.md",
            "build-logs/fa442-pipeline-repair/selection/selection.json",
        ],
    },
    {
        "branch": "fix/fa443-blocker-body-tournament-20260810",
        "workflow_name": "FA443 repaired-pipeline blocker body tournament",
        "report_paths": [
            "build-logs/fa443-blocker-tournament/final/STATUS.json",
            "build-logs/fa443-blocker-tournament/final/STATUS.md",
            "build-logs/fa443-blocker-tournament/selection/selection.json",
        ],
    },
]


def request(path_or_url: str) -> bytes:
    url = path_or_url if path_or_url.startswith("http") else API + path_or_url
    req = urllib.request.Request(url)
    req.add_header("Accept", "application/vnd.github+json")
    req.add_header("X-GitHub-Api-Version", "2022-11-28")
    req.add_header("User-Agent", "fa442-status-dashboard")
    if TOKEN:
        req.add_header("Authorization", f"Bearer {TOKEN}")
    with urllib.request.urlopen(req, timeout=120) as response:
        return response.read()


def api(path_or_url: str) -> Any:
    return json.loads(request(path_or_url).decode("utf-8"))


def latest_run(branch: str, workflow_name: str) -> dict[str, Any] | None:
    encoded = urllib.parse.quote(branch, safe="")
    payload = api(f"/repos/{REPOSITORY}/actions/runs?branch={encoded}&per_page=100")
    rows = [
        row for row in payload.get("workflow_runs", [])
        if row.get("name") == workflow_name
    ]
    return rows[0] if rows else None


def jobs(run_id: int) -> list[dict[str, Any]]:
    payload = api(f"/repos/{REPOSITORY}/actions/runs/{run_id}/jobs?per_page=100")
    return payload.get("jobs", [])


def artifacts(run_id: int) -> list[dict[str, Any]]:
    payload = api(f"/repos/{REPOSITORY}/actions/runs/{run_id}/artifacts?per_page=100")
    return payload.get("artifacts", [])


def content(branch: str, path: str) -> dict[str, Any]:
    encoded_path = urllib.parse.quote(path, safe="/")
    encoded_ref = urllib.parse.quote(branch, safe="")
    try:
        row = api(f"/repos/{REPOSITORY}/contents/{encoded_path}?ref={encoded_ref}")
    except urllib.error.HTTPError as exc:
        if exc.code == 404:
            return {"path": path, "exists": False}
        raise
    raw = base64.b64decode(row["content"])
    result = {
        "path": path,
        "exists": True,
        "blob_sha": row.get("sha"),
        "bytes": len(raw),
        "text": raw.decode("utf-8", errors="replace"),
    }
    if path.endswith(".json"):
        try:
            result["json"] = json.loads(result["text"])
        except Exception as exc:
            result["json_error"] = repr(exc)
    return result


def simplify_run(run: dict[str, Any] | None) -> dict[str, Any]:
    if run is None:
        return {"exists": False}
    run_id = int(run["id"])
    job_rows = jobs(run_id)
    artifact_rows = artifacts(run_id)
    return {
        "exists": True,
        "id": run_id,
        "html_url": run.get("html_url"),
        "status": run.get("status"),
        "conclusion": run.get("conclusion"),
        "head_branch": run.get("head_branch"),
        "head_sha": run.get("head_sha"),
        "created_at": run.get("created_at"),
        "updated_at": run.get("updated_at"),
        "jobs": [
            {
                "id": job.get("id"),
                "name": job.get("name"),
                "status": job.get("status"),
                "conclusion": job.get("conclusion"),
                "steps": [
                    {
                        "number": step.get("number"),
                        "name": step.get("name"),
                        "status": step.get("status"),
                        "conclusion": step.get("conclusion"),
                    }
                    for step in job.get("steps", [])
                ],
            }
            for job in job_rows
        ],
        "artifacts": [
            {
                "id": a.get("id"),
                "name": a.get("name"),
                "size_in_bytes": a.get("size_in_bytes"),
                "expired": a.get("expired"),
                "digest": a.get("digest"),
            }
            for a in artifact_rows
        ],
    }


def classification_from_reports(reports: list[dict[str, Any]]) -> str:
    for report in reports:
        data = report.get("json")
        if not isinstance(data, dict):
            continue
        for key in ("final_classification", "classification"):
            value = data.get(key)
            if value:
                return str(value)
    return "NO_COMMITTED_REPORT"


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    dashboard = {
        "generated_at_epoch": int(time.time()),
        "repository": REPOSITORY,
        "targets": [],
    }
    for target in TARGETS:
        run = latest_run(target["branch"], target["workflow_name"])
        reports = [content(target["branch"], path) for path in target["report_paths"]]
        dashboard["targets"].append({
            **target,
            "run": simplify_run(run),
            "reports": reports,
            "lean_or_pipeline_classification": classification_from_reports(reports),
        })
    (OUT / "STATUS.json").write_text(
        json.dumps(dashboard, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    lines = [
        "# FA442 / FA443 STATUS DASHBOARD",
        "",
        "Workflow conclusion and Lean/pipeline classification are deliberately shown separately.",
        "",
        "branch | run | workflow status | workflow conclusion | Lean/pipeline classification | artifacts",
        "--- | --- | --- | --- | --- | ---",
    ]
    for target in dashboard["targets"]:
        run = target["run"]
        run_cell = f"[{run.get('id')}]({run.get('html_url')})" if run.get("exists") else "NONE"
        artifacts_cell = ", ".join(
            f"{a['name']} (`{a['id']}`)" for a in run.get("artifacts", [])
        ) or "NONE"
        lines.append(
            f"`{target['branch']}` | {run_cell} | {run.get('status', '')} | "
            f"{run.get('conclusion', '')} | **{target['lean_or_pipeline_classification']}** | "
            f"{artifacts_cell}"
        )
    lines.extend(["", "## Job steps", ""])
    for target in dashboard["targets"]:
        lines.append(f"### `{target['branch']}`")
        lines.append("")
        for job in target["run"].get("jobs", []):
            lines.append(
                f"- `{job['name']}`: status `{job['status']}`, conclusion `{job['conclusion']}`"
            )
            for step in job.get("steps", []):
                lines.append(
                    f"  - {step['number']}. {step['name']}: `{step['status']}` / `{step['conclusion']}`"
                )
        if not target["run"].get("jobs"):
            lines.append("- No run/jobs recovered yet.")
        lines.append("")
    (OUT / "STATUS.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps(dashboard, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
