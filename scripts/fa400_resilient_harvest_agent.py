#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "scripts" / "fa399_harvest_combinator_agent.py"

spec = importlib.util.spec_from_file_location("fa399", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 399 harvester/combinator")
fa399 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa399)
fa391 = fa399.fa391

cycle = int(os.environ.get("FA400_CYCLE", "1"))
TOKEN = os.environ.get("GITHUB_TOKEN", "")
ENDPOINT = os.environ.get("GITHUB_MODELS_ENDPOINT", "https://models.github.ai/inference/chat/completions")
HARVEST_BRANCHES = [
    "fix/fa398-self-dispatch-priority-loop-20260809",
    "fix/fa399-harvest-combinator-loop-20260809",
]


def robust_call_model(model: str, prompt: str) -> tuple[str, str]:
    if not TOKEN:
        return model, "ERROR: missing GITHUB_TOKEN"
    temperature = 0.05 + 0.1 * (cycle % 5)
    payload = {
        "model": model,
        "messages": [
            {
                "role": "system",
                "content": (
                    "You repair Lean 4.33.0-rc1 code against the checked-out Mathlib. "
                    "Never change theorem statements or assumptions. Never use sorry, admit, "
                    "axiom, unsafe, native_decide, or Lean.ofReduceBool. Return JSON only."
                ),
            },
            {"role": "user", "content": prompt},
        ],
        "temperature": temperature,
        "max_tokens": 9000,
    }
    body = json.dumps(payload).encode("utf-8")
    failures: list[str] = []
    for attempt in range(1, 5):
        request = urllib.request.Request(
            ENDPOINT,
            data=body,
            headers={
                "Authorization": f"Bearer {TOKEN}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "X-GitHub-Api-Version": "2022-11-28",
            },
            method="POST",
        )
        try:
            with urllib.request.urlopen(request, timeout=240) as response:
                result = json.loads(response.read().decode("utf-8"))
            return model, str(result["choices"][0]["message"]["content"])
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")[:4000]
            failures.append(f"attempt {attempt}: HTTP {exc.code}: {detail}")
            if exc.code not in {408, 409, 425, 429, 500, 502, 503, 504}:
                break
        except (urllib.error.URLError, TimeoutError, KeyError, ValueError) as exc:
            failures.append(f"attempt {attempt}: {type(exc).__name__}: {exc}")
        time.sleep(min(60, 8 * attempt))
    return model, "ERROR: " + " | ".join(failures)


fa391.call_model = robust_call_model


def git_run(args: list[str], timeout: int = 300) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
        check=False,
    )


def metric_key(metric: dict[str, object]) -> tuple[int, int, int]:
    return (
        1 if int(metric["exit_code"]) == 0 else 0,
        int(metric["first_line"]),
        -int(metric["errors"]),
    )


def harvest_all() -> dict[str, object]:
    fa399.OUT.mkdir(parents=True, exist_ok=True)
    target = fa399.TARGET
    initial_text = target.read_text(encoding="utf-8")
    headers = fa391.public_headers(initial_text)
    best_text = initial_text
    best_metric = fa391.compile_file(target, f"fa400-current-c{cycle}", max_errors=14)
    report: dict[str, object] = {
        "cycle": cycle,
        "current": best_metric,
        "candidates": [],
        "selected": "current",
    }
    for branch in HARVEST_BRANCHES:
        remote_ref = f"refs/remotes/origin/{branch}"
        fetch = git_run([
            "git", "fetch", "origin",
            f"refs/heads/{branch}:{remote_ref}",
        ])
        entry: dict[str, object] = {
            "branch": branch,
            "fetch_exit_code": fetch.returncode,
            "fetch_tail": fetch.stdout[-3000:],
        }
        if fetch.returncode != 0:
            report["candidates"].append(entry)
            continue
        show = git_run([
            "git", "show",
            f"{remote_ref}:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
        ], timeout=180)
        entry["show_exit_code"] = show.returncode
        if show.returncode != 0 or not show.stdout.strip():
            entry["show_tail"] = show.stdout[-3000:]
            report["candidates"].append(entry)
            continue
        candidate_text = show.stdout
        if fa391.public_headers(candidate_text) != headers:
            entry["rejected"] = "public-header mismatch"
            report["candidates"].append(entry)
            continue
        audit = fa391.audit_text(candidate_text)
        if any(audit.values()):
            entry["rejected"] = {"forbidden-token audit": audit}
            report["candidates"].append(entry)
            continue
        target.write_text(candidate_text, encoding="utf-8")
        metric = fa391.compile_file(
            target,
            f"fa400-{branch.split('/')[-1]}-c{cycle}",
            max_errors=14,
        )
        entry["metric"] = metric
        report["candidates"].append(entry)
        if metric_key(metric) > metric_key(best_metric):
            best_metric = metric
            best_text = candidate_text
            report["selected"] = branch
    target.write_text(best_text, encoding="utf-8")
    report["selected_metric"] = best_metric
    report["selected_sha256"] = fa391.sha(target)
    return report


def main() -> int:
    fa399.OUT.mkdir(parents=True, exist_ok=True)
    harvest = harvest_all()
    combinator = fa399.deterministic_instance_search()
    current = {
        "cycle": cycle,
        "resilient_harvest": harvest,
        "combinator": combinator,
        "source_sha256_before_model": fa391.sha(fa399.TARGET),
    }
    (fa399.OUT / "CURRENT.json").write_text(json.dumps(current, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(current, indent=2))
    return fa391.main()


if __name__ == "__main__":
    raise SystemExit(main())
