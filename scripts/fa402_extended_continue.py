#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "scripts" / "fa401_extended_frontier.py"
spec = importlib.util.spec_from_file_location("fa401_for_fa402", SOURCE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {SOURCE}")
S = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = S
spec.loader.exec_module(S)

S.BRANCH = "fix/fa402-extended-continue-20260809"
S.EVIDENCE = ROOT / "build-logs" / "fa402-extended-continue"
S.STATE = S.EVIDENCE / "STATE.json"
S.FINAL = S.EVIDENCE / "FINAL_STATUS.json"
S.MARKER = S.EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"

_original_fetch = S.fetch_sources

def fetch_sources_with_pass401():
    sources = _original_fetch()
    for label, branch in {
        "pass401": "fix/fa401-extended-frontier-20260809",
        "pass400": "fix/fa400-fast-frontier-20260809",
        "pass399": "fix/fa399-single-run-proof-body-loop-20260809",
        "pass398": "fix/fa398-single-run-tournament-loop-20260809",
        "pr9": "ci/fa319-isolated-20260807",
    }.items():
        source = S.M.fetch_branch_source(branch, f"fa402-{label}")
        if source is not None:
            sources[label] = source
    return sources

S.fetch_sources = fetch_sources_with_pass401

if __name__ == "__main__":
    raise SystemExit(S.main())
