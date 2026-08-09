#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PVS = ROOT / "PrimalitySheafVerification"
BRANCH = "fix/fa407-restored-hybrid-20260809"
EVIDENCE = ROOT / "build-logs" / "fa407-restored-hybrid"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


B = load("fa396_original_for_fa407", ROOT / "scripts" / "fa396_proof_body_persistent.py")
E = load("fa401_for_fa407", ROOT / "scripts" / "fa401_extended_frontier.py")


def commit_progress(label: str) -> None:
    targets = [
        PVS / "Mock2_FunctionalAnalysis.lean",
        PVS / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PVS.glob("Mock3*.lean")),
        PVS / "QYM.lean",
    ]
    subprocess.run(["git", "add", *(str(p.relative_to(ROOT)) for p in targets if p.exists())], cwd=ROOT, check=True)
    if subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=ROOT).returncode != 0:
        subprocess.run(["git", "commit", "-m", f"{label} [skip ci]"], cwd=ROOT, check=True)
        subprocess.run(["git", "push", "origin", f"HEAD:{BRANCH}"], cwd=ROOT, check=True)


def main() -> int:
    token = __import__("os").environ.get("GITHUB_TOKEN", "")
    if not token:
        raise SystemExit("GITHUB_TOKEN required")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    fa = PVS / "Mock2_FunctionalAnalysis.lean"

    candidates: dict[str, str] = {}
    for label, branch in {
        "pass407-current": BRANCH,
        "pass406": "fix/fa406-self-contained-20260809",
        "pass405": "fix/fa405-ordered-self-chain-20260809",
        "pass404": "fix/fa404-extended-frontier-20260809",
        "pass403": "fix/fa403-hybrid-continue-20260809",
        "pass402": "fix/fa402-extended-continue-20260809",
        "pass401": "fix/fa401-extended-frontier-20260809",
        "pass400": "fix/fa400-fast-frontier-20260809",
        "pass389": "fix/fa389-declaration-beam-20260809",
        "pr9": "ci/fa319-isolated-20260807",
    }.items():
        try:
            source = E.M.fetch_branch_source(branch, f"fa407-{label}")
        except Exception:
            source = None
        if source is not None and len(source.encode("utf-8")) > 100_000:
            candidates[label] = source
    if candidates:
        _, metric, selected = E.select_baseline(fa, candidates)
        (EVIDENCE / "selected-baseline.json").write_text(
            json.dumps({"selected": selected, "metric": metric.to_json()}, indent=2), encoding="utf-8"
        )
        commit_progress("fix: select PASS 407 hybrid baseline")

    models = B.choose_models(B.catalog_models(token), 0)
    body_metric = B.repair_body(
        fa,
        EVIDENCE / "proof-body",
        token,
        models,
        rounds=10,
        max_candidates=6,
        max_errors=260,
    )
    (EVIDENCE / "proof-body-status.json").write_text(
        json.dumps(body_metric.to_json(), indent=2), encoding="utf-8"
    )
    commit_progress("fix: advance PASS 407 proof-body frontier")

    E.BRANCH = BRANCH
    E.EVIDENCE = EVIDENCE / "extended"
    E.STATE = E.EVIDENCE / "STATE.json"
    E.FINAL = E.EVIDENCE / "FINAL_STATUS.json"
    E.MARKER = E.EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"
    original_fetch = E.fetch_sources

    def fetch_with_current_chain():
        sources = original_fetch()
        for label, branch in {
            "pass407-current": BRANCH,
            "pass406": "fix/fa406-self-contained-20260809",
            "pass405": "fix/fa405-ordered-self-chain-20260809",
            "pass404": "fix/fa404-extended-frontier-20260809",
            "pass403": "fix/fa403-hybrid-continue-20260809",
            "pass389": "fix/fa389-declaration-beam-20260809",
        }.items():
            try:
                source = E.M.fetch_branch_source(branch, f"fa407-extended-{label}")
            except Exception:
                source = None
            if source is not None and len(source.encode("utf-8")) > 100_000:
                sources[label] = source
        return sources

    E.fetch_sources = fetch_with_current_chain
    old_argv = sys.argv[:]
    try:
        sys.argv = [str(ROOT / "scripts" / "fa401_extended_frontier.py"), "--rounds", "24", "--candidates", "8"]
        rc = E.main()
    finally:
        sys.argv = old_argv

    if E.FINAL.exists():
        (EVIDENCE / "FINAL_STATUS.json").write_bytes(E.FINAL.read_bytes())
    if E.MARKER.exists():
        (EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS").write_bytes(E.MARKER.read_bytes())
    commit_progress("fix: preserve PASS 407 ordered verification state")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
