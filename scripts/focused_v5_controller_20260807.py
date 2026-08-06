#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import subprocess
import time
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path

REPOSITORY = os.environ["GITHUB_REPOSITORY"]
TOKEN = os.environ["GH_TOKEN"]
BRANCH = "fix/primality-sheaf-clean-build"
API = f"https://api.github.com/repos/{REPOSITORY}"


@dataclass(frozen=True)
class Phase:
    name: str
    marker: str
    failure: str
    retry: str
    max_retries: int


PHASES = [
    Phase(
        "Focused phased Mock2 Advanced candidate v5",
        ".ci/focused/m2a_candidate_v5.json",
        ".ci/focused/m2a_candidate_v5_failure.json",
        ".ci/focused/m2a_candidate_v5_retry.txt",
        3,
    ),
    Phase(
        "Focused phased Mock2 Advanced direct-source v5",
        ".ci/focused/m2a_direct_pass_v5.json",
        ".ci/focused/m2a_direct_v5_failure.json",
        ".ci/focused/m2a_direct_v5_retry.txt",
        3,
    ),
    Phase(
        "Focused phased FunctionalAnalysis candidate v5",
        ".ci/focused/fa_candidate_v5.json",
        ".ci/focused/fa_candidate_v5_failure.json",
        ".ci/focused/fa_candidate_v5_retry.txt",
        3,
    ),
    Phase(
        "Focused phased FunctionalAnalysis direct-source v5",
        ".ci/focused/fa_direct_pass_v5.json",
        ".ci/focused/fa_direct_v5_failure.json",
        ".ci/focused/fa_direct_v5_retry.txt",
        3,
    ),
    Phase(
        "Focused phased QYM final direct-source v5",
        ".ci/focused/focused_direct_pass_v5.json",
        ".ci/focused/qym_direct_v5_failure.json",
        ".ci/focused/qym_direct_v5_retry.txt",
        3,
    ),
]

ACTIVE = {"queued", "in_progress", "waiting", "pending", "requested"}


def request_json(url: str) -> dict:
    req = urllib.request.Request(
        url,
        headers={
            "Authorization": f"Bearer {TOKEN}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "focused-v5-controller",
        },
    )
    with urllib.request.urlopen(req, timeout=60) as response:
        return json.load(response)


def branch_file_exists(path: str) -> bool:
    url = f"{API}/contents/{path}?ref={BRANCH.replace('/', '%2F')}"
    try:
        request_json(url)
        return True
    except urllib.error.HTTPError as exc:
        if exc.code == 404:
            return False
        raise


def branch_file_text(path: str) -> str | None:
    raw = subprocess.run(
        ["git", "show", f"origin/{BRANCH}:{path}"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return raw.stdout if raw.returncode == 0 else None


def current_phase() -> Phase | None:
    for phase in PHASES:
        if not branch_file_exists(phase.marker):
            return phase
    return None


def workflow_runs() -> list[dict]:
    encoded = BRANCH.replace("/", "%2F")
    data = request_json(f"{API}/actions/runs?branch={encoded}&per_page=100")
    return data.get("workflow_runs", [])


def runs_for(name: str) -> list[dict]:
    return sorted(
        [run for run in workflow_runs() if run.get("name") == name],
        key=lambda run: run.get("id", 0),
        reverse=True,
    )


def retry_count(phase: Phase) -> int:
    subprocess.run(["git", "fetch", "origin", BRANCH], check=True, stdout=subprocess.DEVNULL)
    text = branch_file_text(phase.retry)
    if text is None:
        return 0
    text = text.strip()
    return int(text) if text.isdigit() else 0


def trigger_retry(phase: Phase, number: int) -> bool:
    workdir = Path("/tmp/focused-v5-controller-retry")
    subprocess.run(["rm", "-rf", str(workdir)], check=True)
    clone_url = f"https://x-access-token:{TOKEN}@github.com/{REPOSITORY}.git"
    subprocess.run(
        ["git", "clone", "--branch", BRANCH, "--single-branch", clone_url, str(workdir)],
        check=True,
        stdout=subprocess.DEVNULL,
    )
    path = workdir / phase.retry
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"{number}\n")
    subprocess.run(["git", "config", "user.name", "github-actions[bot]"], cwd=workdir, check=True)
    subprocess.run(
        ["git", "config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com"],
        cwd=workdir,
        check=True,
    )
    subprocess.run(["git", "add", phase.retry], cwd=workdir, check=True)
    changed = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=workdir).returncode != 0
    if not changed:
        return False
    subprocess.run(
        ["git", "commit", "-m", f"ci: controller retry {phase.name} ({number}/{phase.max_retries})"],
        cwd=workdir,
        check=True,
        stdout=subprocess.DEVNULL,
    )
    for attempt in range(1, 5):
        pushed = subprocess.run(
            ["git", "push", "origin", f"HEAD:{BRANCH}"],
            cwd=workdir,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if pushed.returncode == 0:
            return True
        subprocess.run(["git", "fetch", "origin", BRANCH], cwd=workdir, check=True, stdout=subprocess.DEVNULL)
        rebased = subprocess.run(
            ["git", "rebase", f"origin/{BRANCH}"], cwd=workdir, stdout=subprocess.DEVNULL
        )
        if rebased.returncode != 0:
            return False
        time.sleep(attempt * 2)
    return False


def write_controller_failure(phase: Phase, reason: str, latest: dict | None) -> None:
    workdir = Path("/tmp/focused-v5-controller-failure")
    subprocess.run(["rm", "-rf", str(workdir)], check=True)
    clone_url = f"https://x-access-token:{TOKEN}@github.com/{REPOSITORY}.git"
    subprocess.run(
        ["git", "clone", "--branch", BRANCH, "--single-branch", clone_url, str(workdir)],
        check=True,
        stdout=subprocess.DEVNULL,
    )
    report_path = workdir / ".ci/focused/focused_v5_controller_failure.json"
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report = {
        "status": "FAIL",
        "phase": phase.name,
        "reason": reason,
        "failure_marker": phase.failure if branch_file_exists(phase.failure) else None,
        "latest_workflow_run": {
            key: latest.get(key) if latest else None
            for key in ("id", "name", "status", "conclusion", "html_url", "head_sha", "run_attempt")
        },
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    subprocess.run(["git", "config", "user.name", "github-actions[bot]"], cwd=workdir, check=True)
    subprocess.run(
        ["git", "config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com"],
        cwd=workdir,
        check=True,
    )
    subprocess.run(["git", "add", str(report_path.relative_to(workdir))], cwd=workdir, check=True)
    if subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=workdir).returncode == 0:
        return
    subprocess.run(
        ["git", "commit", "-m", "ci: record focused v5 controller terminal failure"],
        cwd=workdir,
        check=True,
        stdout=subprocess.DEVNULL,
    )
    subprocess.run(["git", "push", "origin", f"HEAD:{BRANCH}"], cwd=workdir, check=False)


def main() -> int:
    deadline = time.time() + 5 * 60 * 60 + 40 * 60
    last_trigger: dict[str, float] = {}
    while time.time() < deadline:
        subprocess.run(["git", "fetch", "origin", BRANCH], check=True, stdout=subprocess.DEVNULL)
        phase = current_phase()
        if phase is None:
            print("FOCUSED_V5_CONTROLLER_PASS", flush=True)
            return 0

        runs = runs_for(phase.name)
        active = [run for run in runs if run.get("status") in ACTIVE]
        latest = runs[0] if runs else None
        if active:
            print(
                f"waiting phase={phase.name} run={active[0].get('id')} status={active[0].get('status')}",
                flush=True,
            )
            time.sleep(60)
            continue

        count = retry_count(phase)
        latest_conclusion = latest.get("conclusion") if latest else None
        latest_age_guard = last_trigger.get(phase.name, 0)
        if time.time() - latest_age_guard < 180:
            time.sleep(30)
            continue

        if count >= phase.max_retries:
            reason = f"retry limit {phase.max_retries} reached; latest conclusion={latest_conclusion}"
            write_controller_failure(phase, reason, latest)
            print(reason, flush=True)
            return 1

        next_count = count + 1
        print(
            f"triggering phase={phase.name} retry={next_count}/{phase.max_retries} latest={latest_conclusion}",
            flush=True,
        )
        if trigger_retry(phase, next_count):
            last_trigger[phase.name] = time.time()
        else:
            time.sleep(60)
        time.sleep(30)

    phase = current_phase()
    if phase is not None:
        latest = runs_for(phase.name)
        write_controller_failure(phase, "controller wall-clock timeout", latest[0] if latest else None)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
