#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import shutil
import sys
from dataclasses import asdict
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
BUILD = ROOT / ".lake/build/lib/lean/PrimalitySheafVerification"

spec = importlib.util.spec_from_file_location("fa427_screen_common", ROOT / "scripts/fa425_run_strict_controller.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load direct compiler helper")
common = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = common
spec.loader.exec_module(common)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--prepared", required=True)
    ap.add_argument("--index", type=int, required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()

    prepared = Path(args.prepared)
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    common.LOG_DIR = output
    manifest = json.loads((prepared / "MANIFEST.json").read_text(encoding="utf-8"))
    by_index = {int(item["index"]): item for item in manifest["candidates"]}
    if args.index not in by_index:
        raise SystemExit(f"candidate index {args.index} not found")
    item = by_index[args.index]
    candidate = prepared / "candidates" / item["file"]
    if common.sha(candidate) != item["source_sha256"] or common.line_count(candidate) != item["line_count"]:
        raise SystemExit("candidate artifact identity mismatch")

    BUILD.mkdir(parents=True, exist_ok=True)
    for prerequisite in (prepared / "prerequisites").glob("*.*lean"):
        shutil.copy2(prerequisite, BUILD / prerequisite.name)
    shutil.copy2(candidate, SOURCE)
    metric = common.compile_source("Mock2_FunctionalAnalysis", f"candidate-{args.index:03d}", 1)
    if metric.source_sha256 != item["source_sha256"] or metric.line_count != item["line_count"]:
        raise SystemExit("direct metric/source identity mismatch")
    result = {
        "candidate": item,
        "metric": asdict(metric),
        "classification": "CANDIDATE",
        "authority": "direct Lean CLI",
        "maxErrors_cap": 1,
        "maxErrors_interpretation": "screening stops after the first actual error; not a total-error count",
    }
    (output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    shutil.copy2(candidate, output / "candidate.lean")
    common.write_context(metric, candidate, output / "FIRST_ERROR_CONTEXT.txt")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
