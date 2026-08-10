#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import sys
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
EVIDENCE = ROOT / "build-logs/fa440-parallel-direct-solver/UPSTREAM.json"
SOLVER = ROOT / "scripts/fa440_parallel_direct_solver.py"
EXPECTED_LINES = 60453


def load_solver():
    spec = importlib.util.spec_from_file_location("fa441_loaded_fa440", SOLVER)
    if spec is None or spec.loader is None:
        raise RuntimeError("unable to import FA440 solver")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main() -> int:
    if not SOURCE.exists() or not EVIDENCE.exists():
        raise RuntimeError("checked-in upstream source/evidence is missing")
    data = SOURCE.read_bytes()
    text = data.decode("utf-8")
    source_sha = hashlib.sha256(data).hexdigest()
    line_count = data.count(b"\n") + (0 if data.endswith(b"\n") else 1)
    evidence = json.loads(EVIDENCE.read_text(encoding="utf-8"))
    selected = evidence.get("selected", {})
    authority = evidence.get("authority")
    classification = evidence.get("classification")
    exit_code = int(selected.get("exit_code", 999))
    first_line = int(selected.get("first_error_line", 0))
    first_col = int(selected.get("first_error_col", 0))
    valid = (
        classification == "VERIFIED"
        and authority
        == "direct Lean CLI actual repository-path confirmation"
        and selected.get("source_sha256") == source_sha
        and line_count == EXPECTED_LINES
        and (exit_code == 0 or first_line >= 31726)
    )
    if not valid:
        raise RuntimeError(
            "upstream source/evidence identity failed: "
            f"classification={classification}, authority={authority}, "
            f"selected_sha={selected.get('source_sha256')}, actual_sha={source_sha}, "
            f"lines={line_count}, exit={exit_code}, first={first_line}:{first_col}"
        )

    solver = load_solver()
    solver.PASS423_SHA = source_sha
    solver.MINIMUM_FRONTIER = first_line if exit_code != 0 else 0

    provenance = {
        "source": "FA440 checked-in direct-verified source",
        "source_sha256": source_sha,
        "line_count": line_count,
        "FA_exit": exit_code,
        "FA_first_error_line": first_line,
        "FA_first_error_col": first_col,
        "upstream_branch": os.environ.get("UPSTREAM_BRANCH"),
        "upstream_commit": os.environ.get("UPSTREAM_COMMIT"),
        "evidence_path": str(EVIDENCE),
    }
    solver.recover_verified_baseline = lambda: (text, provenance)
    return int(solver.main())


if __name__ == "__main__":
    raise SystemExit(main())
