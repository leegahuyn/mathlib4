#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PVS = ROOT / "PrimalitySheafVerification"
BRANCH = "fix/fa403-hybrid-continue-20260809"
EVIDENCE = ROOT / "build-logs" / "fa403-hybrid"


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


B = load("fa396_for_fa403", ROOT / "scripts" / "fa396_proof_body_persistent.py")
E = load("fa401_for_fa403", ROOT / "scripts" / "fa401_extended_frontier.py")


def commit(label: str) -> None:
    targets = [
        PVS / "Mock2_FunctionalAnalysis.lean",
        PVS / "Mock2_FunctionalAnalysis_Integrated.lean",
        *sorted(PVS.glob("Mock3*.lean")),
        PVS / "QYM.lean",
    ]
    subprocess.run(["git", "add", *(str(p.relative_to(ROOT)) for p in targets if p.exists())], cwd=ROOT, check=True)
    if subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=ROOT).returncode != 0:
        subprocess.run(["git", "commit", "-m", label], cwd=ROOT, check=True)
        subprocess.run(["git", "push", "origin", f"HEAD:{BRANCH}"], cwd=ROOT, check=True)


def main() -> int:
    token = os.environ.get("GITHUB_TOKEN", "")
    if not token:
        raise SystemExit("GITHUB_TOKEN required")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    fa = PVS / "Mock2_FunctionalAnalysis.lean"

    candidates = {}
    for label, branch in {
        "pass402": "fix/fa402-extended-continue-20260809",
        "pass401": "fix/fa401-extended-frontier-20260809",
        "pass400": "fix/fa400-fast-frontier-20260809",
        "pass399": "fix/fa399-single-run-proof-body-loop-20260809",
        "pass398": "fix/fa398-single-run-tournament-loop-20260809",
        "pr9": "ci/fa319-isolated-20260807",
    }.items():
        source = E.M.fetch_branch_source(branch, f"fa403-{label}")
        if source is not None:
            candidates[label] = source
    _, metric, selected = E.select_baseline(fa, candidates)
    (EVIDENCE / "selected-baseline.json").write_text(
        json.dumps({"selected": selected, "metric": metric.to_json()}, indent=2), encoding="utf-8"
    )
    commit("fix: select PASS 403 hybrid baseline")

    models = B.choose_models(B.catalog_models(token), 0)
    body_metric = B.repair_body(
        fa,
        EVIDENCE / "proof-body",
        token,
        models,
        rounds=7,
        max_candidates=6,
        max_errors=220,
    )
    (EVIDENCE / "proof-body-status.json").write_text(json.dumps(body_metric.to_json(), indent=2))
    commit("fix: advance PASS 403 proof-body frontier")

    E.BRANCH = BRANCH
    E.EVIDENCE = EVIDENCE / "extended"
    E.STATE = E.EVIDENCE / "STATE.json"
    E.FINAL = E.EVIDENCE / "FINAL_STATUS.json"
    E.MARKER = E.EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS"
    original_fetch = E.fetch_sources

    def fetch_with_current_chain():
        sources = original_fetch()
        for label, branch in {
            "pass403-current": BRANCH,
            "pass402": "fix/fa402-extended-continue-20260809",
            "pass401": "fix/fa401-extended-frontier-20260809",
            "pass400": "fix/fa400-fast-frontier-20260809",
        }.items():
            source = E.M.fetch_branch_source(branch, f"fa403-extended-{label}")
            if source is not None:
                sources[label] = source
        return sources

    E.fetch_sources = fetch_with_current_chain
    old_argv = sys.argv[:]
    try:
        sys.argv = [str(ROOT / "scripts" / "fa401_extended_frontier.py"), "--rounds", "16", "--candidates", "6"]
        rc = E.main()
    finally:
        sys.argv = old_argv

    final_path = E.FINAL
    if final_path.exists():
        (EVIDENCE / "FINAL_STATUS.json").write_bytes(final_path.read_bytes())
    if E.MARKER.exists():
        (EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS").write_bytes(E.MARKER.read_bytes())
    subprocess.run(
        ["git", "add", str((EVIDENCE / "FINAL_STATUS.json").relative_to(ROOT))] +
        ([str((EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS").relative_to(ROOT))]
         if (EVIDENCE / "ALL_REQUIRED_TARGETS_2X_PASS").exists() else []),
        cwd=ROOT,
        check=True,
    )
    if subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=ROOT).returncode != 0:
        subprocess.run(["git", "commit", "-m", "ci: record PASS 403 hybrid status"], cwd=ROOT, check=True)
        subprocess.run(["git", "push", "origin", f"HEAD:{BRANCH}"], cwd=ROOT, check=True)
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
