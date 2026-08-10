#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import zipfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO = os.environ["GITHUB_REPOSITORY"]
SOURCE_PATH = "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
OUT = Path("status-records/fa425-fa426")
ART = Path("/tmp/fa-status-artifacts")
OUT.mkdir(parents=True, exist_ok=True)
ART.mkdir(parents=True, exist_ok=True)

CONFIGS = [
    ("fix/fa425-strict-theorem-tournament-20260810", "FA425 strict fixed-height blocker theorem tournament"),
    ("fix/fa425b-preheader-instance-tournament-20260810", "FA425b pre-header canonical instance tournament"),
    ("fix/fa425c-instance-unfold-tournament-20260810", "FA425c instance-unfold closing tournament"),
    ("fix/fa425d-derivative-rebundle-20260810", "FA425d derivative rebundling tournament"),
    ("fix/fa426-multiround-cross-donor-20260810", "FA426 multiround cross-donor strict controller"),
    ("fix/fa426b-multiround-importsafe-20260810", "FA426b import-safe multiround strict controller"),
]


def gh_json(endpoint: str) -> Any:
    p = subprocess.run(["gh", "api", "-H", "Accept: application/vnd.github+json", endpoint], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode != 0:
        return {"_error": p.stderr.decode("utf-8", errors="replace")[-2000:]}
    try:
        return json.loads(p.stdout)
    except Exception as exc:
        return {"_error": f"JSON decode: {exc}", "_stdout": p.stdout.decode("utf-8", errors="replace")[-2000:]}


def gh_binary(endpoint: str, destination: Path) -> bool:
    with destination.open("wb") as f:
        p = subprocess.run(["gh", "api", "-H", "Accept: application/vnd.github+json", endpoint], stdout=f, stderr=subprocess.PIPE)
    if p.returncode != 0:
        destination.unlink(missing_ok=True)
        return False
    return destination.exists() and destination.stat().st_size > 0


def branch_source(branch: str, idx: int) -> dict[str, Any]:
    ref = f"refs/remotes/fa-status/{idx}"
    fetch = subprocess.run(
        ["git", "fetch", "--no-tags", "--depth=1", "origin", f"+refs/heads/{branch}:{ref}"],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if fetch.returncode != 0:
        return {"available": False, "error": fetch.stderr.decode("utf-8", errors="replace")[-1500:]}
    show = subprocess.run(["git", "show", f"{ref}:{SOURCE_PATH}"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if show.returncode != 0:
        return {"available": False, "error": show.stderr.decode("utf-8", errors="replace")[-1500:]}
    data = show.stdout
    commit = subprocess.run(["git", "rev-parse", ref], stdout=subprocess.PIPE, text=True, check=False).stdout.strip()
    return {
        "available": True,
        "commit": commit,
        "sha256": hashlib.sha256(data).hexdigest(),
        "line_count": len(data.decode("utf-8", errors="replace").splitlines()),
        "bytes": len(data),
    }


def compact_metric(row: Any) -> Any:
    if not isinstance(row, dict):
        return row
    keys = [
        "label", "stem", "source_sha256", "line_count", "exit_code", "error_headers", "errors",
        "first_error_line", "first_error_col", "first_error_declaration", "olean", "ilean", "max_errors",
    ]
    return {k: row[k] for k in keys if k in row}


def compact_current(obj: dict[str, Any]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    simple = [
        "classification", "stage", "complete", "verified", "strict_promotion", "fa_true_pass",
        "all_required_targets_2x_pass", "source_should_commit", "checked_in_candidate_sha256",
        "selected_source_sha256", "selected_line_count", "candidate_source_sha256", "promoted",
        "metric_improved", "authority", "promotion_rule",
    ]
    for key in simple:
        if key in obj:
            out[key] = obj[key]
    if isinstance(obj.get("baseline"), dict):
        baseline = obj["baseline"]
        out["baseline"] = {
            k: baseline[k] for k in ["classification", "origin", "source_sha256", "line_count", "minimum_frontier", "verified"] if k in baseline
        }
        if isinstance(baseline.get("FA"), dict):
            out["baseline"]["FA"] = compact_metric(baseline["FA"])
    if isinstance(obj.get("selected_metric"), dict):
        out["selected_metric"] = compact_metric(obj["selected_metric"])
    if isinstance(obj.get("promotion"), dict):
        p = obj["promotion"]
        out["promotion"] = {
            "candidate": p.get("candidate"),
            "consistent": p.get("consistent"),
            "screening_metric": compact_metric(p.get("screening_metric") or p.get("screen") or {}),
            "reverify_run1": compact_metric(p.get("reverify_run1") or {}),
            "reverify_run2": compact_metric(p.get("reverify_run2") or {}),
        }
    for key in ["FA_final_run1", "FA_final_run2"]:
        if isinstance(obj.get(key), dict):
            out[key] = compact_metric(obj[key])
    if isinstance(obj.get("trust_audit"), dict):
        out["trust_audit"] = obj["trust_audit"]
    if isinstance(obj.get("downstream"), dict):
        downstream = obj["downstream"]
        out["downstream"] = {
            "complete": downstream.get("complete"),
            "blocked": downstream.get("blocked"),
            "bridge_count": downstream.get("bridge_count"),
        }
    if isinstance(obj.get("rounds"), list):
        compact_rounds = []
        for rnd in obj["rounds"]:
            if not isinstance(rnd, dict):
                continue
            r = {"round": rnd.get("round"), "result": rnd.get("result")}
            if isinstance(rnd.get("baseline"), dict):
                r["baseline"] = compact_metric(rnd["baseline"])
            if isinstance(rnd.get("promotion"), dict):
                p = rnd["promotion"]
                r["promotion"] = {
                    "candidate": p.get("candidate"),
                    "consistent": p.get("consistent"),
                    "reverify_run2": compact_metric(p.get("reverify_run2") or {}),
                }
            compact_rounds.append(r)
        out["rounds"] = compact_rounds
    if isinstance(obj.get("results"), dict):
        out["results"] = {k: compact_metric(v) for k, v in obj["results"].items()}
    return out


def metric_from_current(obj: dict[str, Any]) -> tuple[int, int, int, str] | None:
    if obj.get("fa_true_pass") and isinstance(obj.get("FA_final_run2"), dict):
        row = obj["FA_final_run2"]
        if int(row.get("exit_code", 1)) == 0:
            return (1, 0, 0, "FA_final_run2")
    if obj.get("strict_promotion") and isinstance(obj.get("promotion"), dict):
        row = obj["promotion"].get("reverify_run2", {})
        if isinstance(row, dict):
            return (1 if int(row.get("exit_code", 1)) == 0 else 0, int(row.get("first_error_line", 0)), int(row.get("first_error_col", 0)), "promotion.reverify_run2")
    if isinstance(obj.get("selected_metric"), dict):
        row = obj["selected_metric"]
        return (1 if int(row.get("exit_code", 1)) == 0 else 0, int(row.get("first_error_line", 0)), int(row.get("first_error_col", 0)), "selected_metric")
    baseline = obj.get("baseline")
    if isinstance(baseline, dict) and baseline.get("verified") and isinstance(baseline.get("FA"), dict):
        row = baseline["FA"]
        return (1 if int(row.get("exit_code", 1)) == 0 else 0, int(row.get("first_error_line", 0)), int(row.get("first_error_col", 0)), "baseline.FA")
    return None


def classify(run: dict[str, Any], currents: list[dict[str, Any]]) -> str:
    if any(c.get("classification") == "VERIFIED" or c.get("verified") or c.get("strict_promotion") or c.get("fa_true_pass") for c in currents):
        return "VERIFIED"
    if run.get("status") in {"queued", "in_progress", "waiting", "requested", "pending"}:
        return "CANDIDATE"
    if run.get("conclusion") in {"failure", "cancelled", "timed_out", "action_required", "startup_failure"}:
        return "INFRA FAILURE"
    return "CANDIDATE"


records: list[dict[str, Any]] = []
best: dict[str, Any] | None = None
for index, (branch, expected_name) in enumerate(CONFIGS, 1):
    runs_obj = gh_json(f"/repos/{REPO}/actions/runs?branch={branch}&event=push&per_page=100")
    runs = runs_obj.get("workflow_runs", []) if isinstance(runs_obj, dict) else []
    exact = [r for r in runs if r.get("name") == expected_name]
    run = max(exact or runs, key=lambda r: r.get("run_number", 0), default={})
    source = branch_source(branch, index)
    record: dict[str, Any] = {
        "branch": branch,
        "expected_workflow_name": expected_name,
        "checked_in_source": source,
        "run": {
            k: run.get(k) for k in ["id", "name", "run_number", "status", "conclusion", "event", "head_sha", "created_at", "updated_at", "html_url"]
        } if run else None,
        "jobs": [],
        "artifacts": [],
        "currents": [],
    }
    if run:
        run_id = run["id"]
        jobs_obj = gh_json(f"/repos/{REPO}/actions/runs/{run_id}/jobs?per_page=100")
        for job in jobs_obj.get("jobs", []) if isinstance(jobs_obj, dict) else []:
            record["jobs"].append({
                "id": job.get("id"), "name": job.get("name"), "status": job.get("status"), "conclusion": job.get("conclusion"),
                "steps": [{"name": s.get("name"), "status": s.get("status"), "conclusion": s.get("conclusion"), "number": s.get("number")} for s in job.get("steps", [])],
            })
        arts_obj = gh_json(f"/repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100")
        for art in arts_obj.get("artifacts", []) if isinstance(arts_obj, dict) else []:
            art_id = art.get("id")
            art_record = {k: art.get(k) for k in ["id", "name", "size_in_bytes", "expired", "created_at", "expires_at", "digest"]}
            if art_id and not art.get("expired"):
                zpath = ART / f"{branch.replace('/', '-')}-{art_id}.zip"
                edir = ART / f"{branch.replace('/', '-')}-{art_id}"
                edir.mkdir(parents=True, exist_ok=True)
                if gh_binary(f"/repos/{REPO}/actions/artifacts/{art_id}/zip", zpath):
                    try:
                        with zipfile.ZipFile(zpath) as zf:
                            zf.extractall(edir)
                        art_record["downloaded"] = True
                        art_record["files"] = sum(1 for p in edir.rglob("*") if p.is_file())
                        for current_path in edir.rglob("CURRENT.json"):
                            try:
                                obj = json.loads(current_path.read_text(encoding="utf-8", errors="replace"))
                            except Exception as exc:
                                record["currents"].append({"artifact_id": art_id, "path": str(current_path.relative_to(edir)), "parse_error": str(exc)})
                                continue
                            compact = compact_current(obj)
                            entry = {"artifact_id": art_id, "path": str(current_path.relative_to(edir)), "data": compact}
                            record["currents"].append(entry)
                    except Exception as exc:
                        art_record["downloaded"] = False
                        art_record["extract_error"] = str(exc)
            record["artifacts"].append(art_record)
    current_data = [x.get("data", {}) for x in record["currents"] if isinstance(x.get("data"), dict)]
    record["classification"] = classify(run, current_data)
    metrics = []
    for entry in record["currents"]:
        data = entry.get("data", {})
        metric = metric_from_current(data) if isinstance(data, dict) else None
        if metric:
            metrics.append({"score": list(metric[:3]), "source": metric[3], "artifact_id": entry.get("artifact_id"), "path": entry.get("path"), "data": data})
    if metrics:
        record["best_direct_metric"] = max(metrics, key=lambda x: tuple(x["score"]))
        candidate = {
            "branch": branch,
            "score": record["best_direct_metric"]["score"],
            "classification": record["classification"],
            "checked_in_source": source,
            "evidence": record["best_direct_metric"],
        }
        if record["classification"] == "VERIFIED" and (best is None or tuple(candidate["score"]) > tuple(best["score"])):
            best = candidate
    records.append(record)

summary = {
    "generated_at_utc": datetime.now(timezone.utc).isoformat(),
    "repository": REPO,
    "authority": "direct Lean CLI evidence inside artifact/checked-in records; workflow conclusion is not module status",
    "known_historical": {
        "31725": "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4",
        "31726": "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0",
    },
    "best_verified": best,
    "records": records,
}
(OUT / "STATUS.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
lines = [
    f"generated_at_utc={summary['generated_at_utc']}",
    f"best_verified_branch={(best or {}).get('branch', '')}",
    f"best_verified_score={(best or {}).get('score', '')}",
]
for record in records:
    run = record.get("run") or {}
    metric = record.get("best_direct_metric") or {}
    source = record.get("checked_in_source") or {}
    lines.append(
        f"{record['branch']}: classification={record['classification']} run={run.get('id')} status={run.get('status')} conclusion={run.get('conclusion')} "
        f"source_sha={source.get('sha256')} lines={source.get('line_count')} metric={metric.get('score')}"
    )
(OUT / "STATUS.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
print((OUT / "STATUS.txt").read_text())
