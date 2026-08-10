#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO = os.environ["GITHUB_REPOSITORY"]
TARGET_BRANCH = "fix/fa427-parallel-frontier-loop-20260810"
WORK = Path("/tmp/fa427-watch-worktree")
BEST_SOURCE = Path("/tmp/fa-watch-best.lean")
BEST_META = Path("/tmp/fa-watch-best.json")
WATCH_STATUS = Path("watch-records/fa-verified-source-watch/STATUS.json")
KNOWN = {
    "07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4": (0, 31725, 2),
    "71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0": (0, 31726, 2),
}


def run(args: list[str], cwd: Path | None = None, check: bool = False) -> subprocess.CompletedProcess[bytes]:
    p = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if check and p.returncode != 0:
        raise RuntimeError(f"command failed: {args}\n{p.stderr.decode(errors='replace')[-3000:]}")
    return p


def gh_json(endpoint: str) -> Any:
    p = run(["gh", "api", "-H", "Accept: application/vnd.github+json", endpoint])
    if p.returncode != 0:
        return {"_error": p.stderr.decode("utf-8", errors="replace")[-2000:]}
    return json.loads(p.stdout)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def score_from_status(obj: dict[str, Any]) -> tuple[int, int, int] | None:
    if obj.get("fa_true_pass") and isinstance(obj.get("FA_final_run2"), dict):
        row = obj["FA_final_run2"]
        if int(row.get("exit_code", 1)) == 0:
            return (1, 0, 0)
    if obj.get("strict_promotion") and isinstance(obj.get("promotion"), dict):
        row = obj["promotion"].get("reverify_run2", {})
        if isinstance(row, dict):
            return (1 if int(row.get("exit_code", 1)) == 0 else 0,
                    int(row.get("first_error_line", 0)), int(row.get("first_error_col", 0)))
    if isinstance(obj.get("selected_metric"), dict):
        row = obj["selected_metric"]
        return (1 if int(row.get("exit_code", 1)) == 0 else 0,
                int(row.get("first_error_line", 0)), int(row.get("first_error_col", 0)))
    baseline = obj.get("baseline")
    if isinstance(baseline, dict) and baseline.get("verified") and isinstance(baseline.get("FA"), dict):
        row = baseline["FA"]
        return (1 if int(row.get("exit_code", 1)) == 0 else 0,
                int(row.get("first_error_line", 0)), int(row.get("first_error_col", 0)))
    return None


def current_target_state() -> dict[str, Any]:
    shutil.rmtree(WORK, ignore_errors=True)
    run(["git", "fetch", "--no-tags", "origin", f"+refs/heads/{TARGET_BRANCH}:refs/remotes/fa-watch/target"], check=True)
    run(["git", "worktree", "add", "--detach", str(WORK), "refs/remotes/fa-watch/target"], check=True)
    source = WORK / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
    source_sha = sha(source)
    source_lines = len(source.read_text(encoding="utf-8", errors="replace").splitlines())
    best_score = KNOWN.get(source_sha, (0, 0, 0))
    evidence_path = "known-source-sha" if source_sha in KNOWN else None
    for path in sorted((WORK / "verified-records/fa427").glob("round-*/CURRENT.json")) if (WORK / "verified-records/fa427").exists() else []:
        try:
            obj = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            continue
        expected = obj.get("selected_source_sha256") or obj.get("checked_in_candidate_sha256")
        if expected and expected != source_sha:
            continue
        score = score_from_status(obj)
        if score and score > best_score:
            best_score = score
            evidence_path = str(path.relative_to(WORK))
    trigger = WORK / "fa427-requests/REQUESTED.txt"
    round_match = re.search(r"(?m)^round=(\d+)\s*$", trigger.read_text(encoding="utf-8", errors="replace")) if trigger.exists() else None
    return {
        "source_sha256": source_sha,
        "line_count": source_lines,
        "score": list(best_score),
        "evidence_path": evidence_path,
        "round": int(round_match.group(1)) if round_match else 1,
        "head": run(["git", "rev-parse", "HEAD"], cwd=WORK).stdout.decode().strip(),
    }


def workflow_activity() -> dict[str, Any]:
    obj = gh_json(f"/repos/{REPO}/actions/runs?branch={TARGET_BRANCH}&event=push&per_page=50")
    runs = [r for r in obj.get("workflow_runs", []) if r.get("name") == "FA427 parallel direct-Lean frontier loop"] if isinstance(obj, dict) else []
    latest = max(runs, key=lambda r: int(r.get("run_number", 0)), default={})
    active = latest.get("status") in {"queued", "in_progress", "waiting", "requested", "pending"}
    recent_obj = gh_json(f"/repos/{REPO}/actions/runs?status=in_progress&per_page=100")
    relevant_active = []
    for r in recent_obj.get("workflow_runs", []) if isinstance(recent_obj, dict) else []:
        branch = r.get("head_branch", "")
        if re.match(r"^(?:fix/fa42[5-9]|ops/fa.*status|ops/fa-verified)", branch):
            relevant_active.append({k: r.get(k) for k in ["id", "name", "head_branch", "status", "conclusion", "run_number"]})
    return {
        "latest_target_run": {k: latest.get(k) for k in ["id", "name", "run_number", "status", "conclusion", "head_sha", "created_at", "updated_at"]} if latest else None,
        "target_active": active,
        "relevant_active_runs": relevant_active,
    }


def push_target_trigger(current: dict[str, Any], best: dict[str, Any], cycle: int) -> bool:
    # Re-fetch immediately before writing; abort rather than force if another job
    # changed the branch after our activity check.
    run(["git", "fetch", "--no-tags", "origin", f"+refs/heads/{TARGET_BRANCH}:refs/remotes/fa-watch/target-latest"], check=True)
    latest = run(["git", "rev-parse", "refs/remotes/fa-watch/target-latest"], check=True).stdout.decode().strip()
    if latest != current["head"]:
        return False
    run(["git", "switch", "-C", "fa-watch-target", "refs/remotes/fa-watch/target-latest"], cwd=WORK, check=True)
    trigger = WORK / "fa427-requests/REQUESTED.txt"
    next_round = int(current.get("round", 1)) + 1
    trigger.parent.mkdir(parents=True, exist_ok=True)
    trigger.write_text(
        f"round={next_round}\n"
        f"watch_cycle={cycle}\n"
        f"expected_best_source_sha256={best['source_sha256']}\n"
        f"expected_best_score={best['score']}\n"
        f"previous_target_source_sha256={current['source_sha256']}\n"
        f"previous_target_score={current['score']}\n"
        "authority=direct Lean CLI source-matched evidence\n"
        "fixed_line_count=60453\n",
        encoding="utf-8",
    )
    run(["git", "config", "user.name", "github-actions[bot]"], cwd=WORK, check=True)
    run(["git", "config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com"], cwd=WORK, check=True)
    run(["git", "add", "fa427-requests/REQUESTED.txt"], cwd=WORK, check=True)
    commit = run(["git", "commit", "-m", f"ci: re-trigger FA427 from verified source watch cycle {cycle}"], cwd=WORK)
    if commit.returncode != 0:
        return False
    pushed = run(["git", "push", "origin", f"HEAD:{TARGET_BRANCH}"], cwd=WORK)
    return pushed.returncode == 0


def main() -> None:
    cycle_path = Path("watch-requests/REQUESTED.txt")
    cycle_text = cycle_path.read_text(encoding="utf-8", errors="replace") if cycle_path.exists() else "cycle=1"
    m = re.search(r"(?m)^cycle=(\d+)\s*$", cycle_text)
    cycle = int(m.group(1)) if m else 1
    best_meta = json.loads(BEST_META.read_text(encoding="utf-8"))
    selected = best_meta["selected"]
    best = {
        "source_sha256": selected["source_sha256"],
        "score": selected.get("score", [0, 0, 0]),
        "ref": selected.get("ref"),
        "classification": selected.get("classification"),
        "evidence_path": selected.get("evidence_path"),
    }
    current = current_target_state()
    activity = workflow_activity()
    better = tuple(best["score"]) > tuple(current["score"])
    latest = activity.get("latest_target_run") or {}
    retry_infra = (
        not activity["target_active"] and latest.get("conclusion") in {"failure", "cancelled", "timed_out", "startup_failure"}
        and cycle <= 3 and current.get("evidence_path") is None
    )
    should_trigger = not activity["target_active"] and (better or retry_infra)
    triggered = push_target_trigger(current, best, cycle) if should_trigger else False
    continue_watch = cycle < 8 and (bool(activity["relevant_active_runs"]) or triggered or activity["target_active"])
    status = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "cycle": cycle,
        "best_source_matched_verified": best,
        "current_fa427": current,
        "activity": activity,
        "better_than_current": better,
        "retry_infra": retry_infra,
        "should_trigger": should_trigger,
        "triggered": triggered,
        "continue_watch": continue_watch,
        "classification": "VERIFIED" if best.get("score") else "CANDIDATE",
    }
    WATCH_STATUS.parent.mkdir(parents=True, exist_ok=True)
    WATCH_STATUS.write_text(json.dumps(status, indent=2) + "\n", encoding="utf-8")
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a", encoding="utf-8") as f:
            f.write(f"cycle={cycle}\n")
            f.write(f"triggered={str(triggered).lower()}\n")
            f.write(f"continue_watch={str(continue_watch).lower()}\n")
            f.write(f"next_cycle={cycle + 1 if continue_watch else ''}\n")
    print(json.dumps(status, indent=2))


if __name__ == "__main__":
    main()
