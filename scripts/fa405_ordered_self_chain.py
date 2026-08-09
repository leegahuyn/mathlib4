#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
PVS = ROOT / "PrimalitySheafVerification"
SOURCE = ROOT / "scripts" / "fa401_extended_frontier.py"
spec = importlib.util.spec_from_file_location("fa401_for_fa405", SOURCE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {SOURCE}")
S = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = S
spec.loader.exec_module(S)

BRANCH = "fix/fa405-ordered-self-chain-20260809"
EVIDENCE = ROOT / "build-logs" / "fa405-ordered-self-chain"
S.BRANCH = BRANCH
S.EVIDENCE = EVIDENCE
S.STATE = EVIDENCE / "STATE.json"
S.FINAL = EVIDENCE / "FINAL_STATUS.json"
S.MARKER = EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"

CANDIDATE_BRANCHES = {
    "fa405-current": BRANCH,
    "fa404": "fix/fa404-extended-frontier-20260809",
    "fa403": "fix/fa403-hybrid-continue-20260809",
    "fa402": "fix/fa402-extended-continue-20260809",
    "fa401": "fix/fa401-extended-frontier-20260809",
    "fa400": "fix/fa400-fast-frontier-20260809",
    "fa399": "fix/fa399-harvest-combinator-loop-20260809",
    "fa389": "fix/fa389-declaration-beam-20260809",
    "pr9": "ci/fa319-isolated-20260807",
}


def structurally_valid(source: str) -> bool:
    if len(source.encode("utf-8")) < 100_000:
        return False
    if not any(token in source for token in ("theorem ", "lemma ", "def ", "structure ")):
        return False
    bad = S.M.H.forbidden_counts(source)
    return not any(bad.values())


def fetch_valid_sources() -> dict[str, str]:
    result: dict[str, str] = {}
    for label, branch in CANDIDATE_BRANCHES.items():
        try:
            source = S.M.fetch_branch_source(branch, f"fa405-{label}")
        except Exception:
            source = None
        if source is not None and structurally_valid(source):
            result[label] = source
    return result


_original_fetch = S.fetch_sources


def fetch_sources_with_chain() -> dict[str, str]:
    sources: dict[str, str] = {}
    try:
        sources.update({k: v for k, v in _original_fetch().items() if structurally_valid(v)})
    except Exception:
        pass
    sources.update(fetch_valid_sources())
    if not sources:
        raise RuntimeError("no structurally valid FunctionalAnalysis source candidate")
    return sources


S.fetch_sources = fetch_sources_with_chain


def main() -> int:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    candidates = fetch_valid_sources()
    fa = PVS / "Mock2_FunctionalAnalysis.lean"
    if not fa.exists() or not structurally_valid(fa.read_text(encoding="utf-8")):
        if not candidates:
            raise RuntimeError("checked-in FA source invalid and no valid recovery source found")
        _, metric, selected = S.select_baseline(fa, candidates)
        (EVIDENCE / "preflight-recovery.json").write_text(
            json.dumps({"selected": selected, "metric": metric.to_json()}, indent=2),
            encoding="utf-8",
        )
    old_argv = sys.argv[:]
    try:
        sys.argv = [str(SOURCE), "--rounds", os.environ.get("FA405_ROUNDS", "24"),
                    "--candidates", os.environ.get("FA405_CANDIDATES", "8")]
        return S.main()
    finally:
        sys.argv = old_argv


if __name__ == "__main__":
    raise SystemExit(main())
