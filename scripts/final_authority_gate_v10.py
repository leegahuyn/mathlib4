#!/usr/bin/env python3
"""Final authority v10 controller.

Loads the original auditable controller as a module and changes only the current
successor-branch policy:
* the PR head is the designated authority branch;
* audited mathematical changes are limited to Spt1, Spt3, Mock1_Advanced,
  Mock3 and BuildAll;
* workflow/controller files are classified as execution infrastructure;
* all protected FA / Integrated / QYM identities and every mathematical gate
  remain enforced by the original controller;
* Final13 diagnostics do not stop after an independent root failure.
"""
from __future__ import annotations

import importlib.util
import os
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = ROOT / "scripts/final_authority_gate.py"
BRANCH = os.environ.get("FINAL_AUTHORITY_BRANCH", "gpt/final-authority-batch-v7-20260820")
os.environ["GITHUB_REF_NAME"] = BRANCH

spec = importlib.util.spec_from_file_location("final_authority_gate_original_v10", ORIGINAL)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {ORIGINAL}")
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

mod.AUTHORITY_BRANCH = BRANCH

PERMITTED_ROOT_CHANGES = {
    "PrimalitySheafVerification/Spt1.lean",
    "PrimalitySheafVerification/Spt3.lean",
    "PrimalitySheafVerification/Mock1_Advanced.lean",
}
PERMITTED_PROJECT_PATHS = PERMITTED_ROOT_CHANGES | {
    "PrimalitySheafVerification/Mock3.lean",
    "PrimalitySheafVerification/BuildAll.lean",
    "final_authority_v7_trigger.txt",
    "final_authority_v9_trigger.txt",
}


def changed_paths_audit(source_commit: str) -> dict[str, Any]:
    changed = [
        x for x in mod.git(
            "diff", "--name-only", f"{mod.BASE_COMMIT}..{source_commit}"
        ).splitlines()
        if x
    ]

    def allowed(path: str) -> bool:
        return (
            path in PERMITTED_PROJECT_PATHS
            or path.startswith(".github/workflows/")
            or path.startswith("scripts/")
        )

    unexpected = sorted(path for path in changed if not allowed(path))
    root_paths = {str(path) for _, path, _ in mod.ROOTS}
    root_changes = sorted(set(changed) & root_paths)
    unexpected_root_changes = sorted(set(root_changes) - PERMITTED_ROOT_CHANGES)
    return {
        "base_commit": mod.BASE_COMMIT,
        "source_commit": source_commit,
        "changed_paths": changed,
        "allowed_paths": sorted(PERMITTED_PROJECT_PATHS),
        "allowed_execution_prefixes": [".github/workflows/", "scripts/"],
        "unexpected_paths": unexpected,
        "primary_root_changes": root_changes,
        "permitted_primary_root_changes": sorted(PERMITTED_ROOT_CHANGES),
        "unexpected_primary_root_changes": unexpected_root_changes,
        "pass": not unexpected and not unexpected_root_changes,
    }


mod.changed_paths_audit = changed_paths_audit

_original_compile_sequence = mod.compile_sequence


def compile_sequence(stage: str, paths: list[Path], clean_first: bool) -> dict[str, Any]:
    if stage != "final13_actual_lean":
        return _original_compile_sequence(stage, paths, clean_first)

    protection_before = mod.verify_protected(f"{stage}:before")
    removed = mod.clear_objects(paths) if clean_first else []
    results: list[dict[str, Any]] = []
    for path in paths:
        results.append(mod.compile_one(path, stage))
    protection_after = mod.verify_protected(f"{stage}:after")
    return {
        "stage": stage,
        "clean_first": clean_first,
        "removed_objects": removed,
        "removed_object_count": len(removed),
        "results": results,
        "pass": (
            protection_before["pass"]
            and protection_after["pass"]
            and bool(results)
            and all(x.get("pass") is True for x in results)
        ),
        "protected_before": protection_before,
        "protected_after": protection_after,
    }


mod.compile_sequence = compile_sequence

if __name__ == "__main__":
    raise SystemExit(mod.main())
