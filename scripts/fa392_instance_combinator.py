#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import itertools
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs" / "fa392-instance-combinator"
HELPER = ROOT / "scripts" / "fa391_targeted_priority_agent_v2.py"

spec = importlib.util.spec_from_file_location("fa391", HELPER)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 391 helper")
fa391 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa391)

INSTANCE_RX = re.compile(
    r"^\s*(?:(?:noncomputable|local)\s+)*(?:instance|letI|haveI)\b.*"
    r"(?:NormedSpace|InnerProductSpace|NormedAddCommGroup|CompleteSpace|Module|SMul)"
)


def indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def instance_blocks(lines: list[str], center: int, radius: int = 650) -> list[tuple[int, int, str]]:
    lo = max(0, center - radius - 1)
    hi = min(len(lines), center + radius)
    blocks: list[tuple[int, int, str]] = []
    i = lo
    while i < hi:
        line = lines[i]
        if not INSTANCE_RX.search(line):
            i += 1
            continue
        base_indent = indent(line)
        j = i + 1
        while j < hi:
            current = lines[j]
            stripped = current.strip()
            if not stripped or stripped.startswith("--"):
                j += 1
                continue
            if indent(current) <= base_indent and not current.lstrip().startswith(("where", "|")):
                break
            j += 1
        blocks.append((i, j, "".join(lines[i:j])))
        i = max(j, i + 1)
    return blocks


def candidate_remove(lines: list[str], blocks: list[tuple[int, int, str]], picks: tuple[int, ...]) -> str:
    remove: set[int] = set()
    for index in picks:
        start, end, _ = blocks[index]
        remove.update(range(start, end))
    return "".join(line for idx, line in enumerate(lines) if idx not in remove)


def candidate_demote(lines: list[str], block: tuple[int, int, str]) -> str | None:
    start, end, _ = block
    segment = "".join(lines[start:end])
    changed = re.sub(r"^(\s*)(letI|haveI)\b", r"\1let", segment, count=1, flags=re.M)
    if changed == segment:
        return None
    return "".join(lines[:start]) + changed + "".join(lines[end:])


def candidate_swap(lines: list[str], first: tuple[int, int, str], second: tuple[int, int, str]) -> str | None:
    a0, a1, a = first
    b0, b1, b = second
    if a1 > b0 or b0 - a1 > 8:
        return None
    middle = "".join(lines[a1:b0])
    return "".join(lines[:a0]) + b + middle + a + "".join(lines[b1:])


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    baseline_text = TARGET.read_text(encoding="utf-8")
    headers = fa391.public_headers(baseline_text)
    baseline = fa391.compile_file(TARGET, "fa392-baseline", max_errors=20)
    center = int(baseline["first_line"])
    lines = baseline_text.splitlines(keepends=True)
    blocks = instance_blocks(lines, center)
    manifest = {
        "baseline": baseline,
        "center": center,
        "blocks": [
            {"start": start + 1, "end": end, "preview": text[:1000]}
            for start, end, text in blocks
        ],
        "candidates": [],
    }
    candidates: list[tuple[str, str]] = []
    for i in range(len(blocks)):
        candidates.append((f"remove-{i:02d}", candidate_remove(lines, blocks, (i,))))
        demoted = candidate_demote(lines, blocks[i])
        if demoted is not None:
            candidates.append((f"demote-{i:02d}", demoted))
    for i, j in itertools.combinations(range(len(blocks)), 2):
        if len(candidates) >= 36:
            break
        candidates.append((f"remove-{i:02d}-{j:02d}", candidate_remove(lines, blocks, (i, j))))
        swapped = candidate_swap(lines, blocks[i], blocks[j])
        if swapped is not None:
            candidates.append((f"swap-{i:02d}-{j:02d}", swapped))
    best_text = baseline_text
    best_metric = baseline
    for index, (name, candidate) in enumerate(candidates[:48], 1):
        if candidate == baseline_text:
            continue
        if fa391.public_headers(candidate) != headers:
            continue
        if any(fa391.audit_text(candidate).values()):
            continue
        TARGET.write_text(candidate, encoding="utf-8")
        metric = fa391.compile_file(TARGET, f"fa392-{index:02d}-{name}", max_errors=20)
        manifest["candidates"].append({"name": name, "metric": metric})
        if fa391.better(metric, best_metric):
            best_metric = metric
            best_text = candidate
    TARGET.write_text(best_text, encoding="utf-8")
    manifest["selected"] = best_metric
    manifest["selected_sha256"] = fa391.sha(TARGET)
    (OUT / "selection.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(json.dumps({"baseline": baseline, "selected": best_metric, "blocks": len(blocks)}, indent=2))
    # Continue with the proof/API model repair only after deterministic instance search.
    proc = subprocess.run(
        [
            sys.executable,
            str(HELPER),
            "--rounds", "8",
            "--models-per-round", "6",
        ],
        cwd=ROOT,
        text=True,
    )
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main())
