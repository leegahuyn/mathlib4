#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs" / "fa399-harvest-combinator"
BASE = ROOT / "scripts" / "fa397_canonical_dependency_agent.py"
PASS398_BRANCH = "fix/fa398-self-dispatch-priority-loop-20260809"

spec = importlib.util.spec_from_file_location("fa397", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 397 canonical dependency agent")
fa397 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa397)
fa391 = fa397.fa391

cycle = int(os.environ.get("FA399_CYCLE", "1"))
base_prompt = fa391.prompt_for


def cycle_prompt(path, metric, log, text):
    prompt = base_prompt(path, metric, log, text)
    previous = OUT / "CURRENT.json"
    previous_text = previous.read_text(encoding="utf-8", errors="replace") if previous.exists() else "(none)"
    return (
        prompt
        + f"\n\nThis is PASS 399 autonomous cycle {cycle}. Previous harvest/combinator status:\n"
        + "```json\n"
        + previous_text[-6000:]
        + "\n```\n"
        + "Do not repeat a rejected edit. If the error is an instance-coherence mismatch, "
          "bind the intended NormedSpace/InnerProductSpace/CompleteSpace family explicitly "
          "through local instance arguments or a coherent local letI chain."
    )


fa391.prompt_for = cycle_prompt

LOCAL_INSTANCE_RX = re.compile(
    r"^\s*(?:(?:noncomputable)\s+)?(?:letI|haveI|local\s+instance)\b.*"
    r"(?:NormedSpace|InnerProductSpace|NormedAddCommGroup|CompleteSpace|Module|SMul)"
)


def run(cmd: list[str], timeout: int = 180) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
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


def is_better(candidate: dict[str, object], baseline: dict[str, object]) -> bool:
    return metric_key(candidate) > metric_key(baseline)


def harvest_pass398() -> dict[str, object]:
    OUT.mkdir(parents=True, exist_ok=True)
    current_text = TARGET.read_text(encoding="utf-8")
    current_headers = fa391.public_headers(current_text)
    current_metric = fa391.compile_file(TARGET, f"fa399-current-c{cycle}", max_errors=16)
    report: dict[str, object] = {
        "current": current_metric,
        "selected": "current",
    }
    fetch = run(["git", "fetch", "origin", PASS398_BRANCH], timeout=300)
    report["fetch_exit_code"] = fetch.returncode
    report["fetch_tail"] = fetch.stdout[-4000:]
    if fetch.returncode != 0:
        return report
    show = run(
        [
            "git", "show",
            f"origin/{PASS398_BRANCH}:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean",
        ],
        timeout=120,
    )
    if show.returncode != 0 or not show.stdout.strip():
        report["show_exit_code"] = show.returncode
        report["show_tail"] = show.stdout[-4000:]
        return report
    external_text = show.stdout
    if fa391.public_headers(external_text) != current_headers:
        report["external_rejected"] = "public-header mismatch"
        return report
    if any(fa391.audit_text(external_text).values()):
        report["external_rejected"] = "forbidden-token audit"
        return report
    TARGET.write_text(external_text, encoding="utf-8")
    external_metric = fa391.compile_file(TARGET, f"fa399-harvest398-c{cycle}", max_errors=16)
    report["pass398"] = external_metric
    if is_better(external_metric, current_metric):
        report["selected"] = "pass398"
        report["selected_metric"] = external_metric
    else:
        TARGET.write_text(current_text, encoding="utf-8")
        report["selected_metric"] = current_metric
    return report


def indentation(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def local_instance_blocks(lines: list[str], center_line: int, radius: int = 480) -> list[tuple[int, int, str]]:
    lo = max(0, center_line - radius - 1)
    hi = min(len(lines), center_line + radius)
    blocks: list[tuple[int, int, str]] = []
    i = lo
    while i < hi:
        line = lines[i]
        if not LOCAL_INSTANCE_RX.search(line):
            i += 1
            continue
        base_indent = indentation(line)
        j = i + 1
        while j < hi:
            current = lines[j]
            stripped = current.strip()
            if not stripped or stripped.startswith("--"):
                j += 1
                continue
            if indentation(current) <= base_indent and not current.lstrip().startswith(("where", "|")):
                break
            j += 1
        blocks.append((i, j, "".join(lines[i:j])))
        i = max(j, i + 1)
    return blocks


def remove_blocks(lines: list[str], blocks: list[tuple[int, int, str]], indexes: tuple[int, ...]) -> str:
    removed: set[int] = set()
    for index in indexes:
        start, end, _ = blocks[index]
        removed.update(range(start, end))
    return "".join(line for i, line in enumerate(lines) if i not in removed)


def swap_adjacent(lines: list[str], first: tuple[int, int, str], second: tuple[int, int, str]) -> str | None:
    a0, a1, a = first
    b0, b1, b = second
    if a1 > b0 or b0 - a1 > 10:
        return None
    middle = "".join(lines[a1:b0])
    return "".join(lines[:a0]) + b + middle + a + "".join(lines[b1:])


def deterministic_instance_search() -> dict[str, object]:
    OUT.mkdir(parents=True, exist_ok=True)
    baseline_text = TARGET.read_text(encoding="utf-8")
    headers = fa391.public_headers(baseline_text)
    baseline = fa391.compile_file(TARGET, f"fa399-comb-baseline-c{cycle}", max_errors=12)
    center = int(baseline["first_line"])
    lines = baseline_text.splitlines(keepends=True)
    blocks = local_instance_blocks(lines, center)
    candidates: list[tuple[str, str]] = []
    for i in range(len(blocks)):
        candidates.append((f"remove-{i:02d}", remove_blocks(lines, blocks, (i,))))
    for i in range(len(blocks) - 1):
        candidates.append((f"remove-{i:02d}-{i+1:02d}", remove_blocks(lines, blocks, (i, i + 1))))
        swapped = swap_adjacent(lines, blocks[i], blocks[i + 1])
        if swapped is not None:
            candidates.append((f"swap-{i:02d}-{i+1:02d}", swapped))
    best_text = baseline_text
    best_metric = baseline
    tested: list[dict[str, object]] = []
    for index, (name, candidate) in enumerate(candidates[:18], 1):
        if candidate == baseline_text:
            continue
        if fa391.public_headers(candidate) != headers:
            tested.append({"name": name, "rejected": "public-header mismatch"})
            continue
        if any(fa391.audit_text(candidate).values()):
            tested.append({"name": name, "rejected": "forbidden-token audit"})
            continue
        TARGET.write_text(candidate, encoding="utf-8")
        metric = fa391.compile_file(TARGET, f"fa399-comb-c{cycle}-{index:02d}", max_errors=12)
        tested.append({"name": name, "metric": metric})
        if is_better(metric, best_metric):
            best_metric = metric
            best_text = candidate
    TARGET.write_text(best_text, encoding="utf-8")
    return {
        "baseline": baseline,
        "center_line": center,
        "blocks": [
            {"start": start + 1, "end": end, "preview": text[:1200]}
            for start, end, text in blocks
        ],
        "tested": tested,
        "selected": best_metric,
        "source_sha256": fa391.sha(TARGET),
    }


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    harvest = harvest_pass398()
    combinator = deterministic_instance_search()
    current = {
        "cycle": cycle,
        "harvest": harvest,
        "combinator": combinator,
        "source_sha256_before_model": fa391.sha(TARGET),
    }
    (OUT / "CURRENT.json").write_text(json.dumps(current, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(current, indent=2))
    # Continue through the strict FA 2x -> Integrated/Mock3 2x -> QYM 2x gate.
    return fa391.main()


if __name__ == "__main__":
    raise SystemExit(main())
