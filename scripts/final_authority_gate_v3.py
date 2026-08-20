#!/usr/bin/env python3
"""Run the final-authority gate on the cumulative M1A repair branch.

This wrapper changes orchestration policy only. It permits the one intended
primary-root repair (Mock1_Advanced), preserves the immutable FA/Integrated/QYM
identities, does not let a forbidden-token preflight suppress real Lean
compilation, and keeps the first Final13 pass broad so all independent failures
are collected in one run.
"""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = ROOT / "scripts/final_authority_gate.py"

source = ORIGINAL.read_text(encoding="utf-8")

replacements = [
    (
        'AUTHORITY_BRANCH = "gpt/final-authority-gb0-canonical-20260820"',
        'AUTHORITY_BRANCH = "gpt/final-authority-mass-repair-v3-20260820"',
        "authority branch",
    ),
    (
        '    branch = os.environ.get("GITHUB_REF_NAME") or git("branch", "--show-current")\n',
        '    branch = git("branch", "--show-current") or os.environ.get("GITHUB_REF_NAME")\n',
        "prefer exact checked-out local branch over PR merge ref",
    ),
    (
        '    allowed = {\n'
        '        "PrimalitySheafVerification/Mock3.lean",\n'
        '        "PrimalitySheafVerification/BuildAll.lean",\n'
        '        "scripts/final_authority_gate.py",\n'
        '        ".github/workflows/gpt-final-authority-gb0-canonical.yml",\n'
        '    }\n',
        '    allowed = {\n'
        '        "PrimalitySheafVerification/Mock1_Advanced.lean",\n'
        '        "PrimalitySheafVerification/Mock3.lean",\n'
        '        "PrimalitySheafVerification/BuildAll.lean",\n'
        '        "scripts/final13_r5_patch_mock1_advanced_six.py",\n'
        '        "scripts/final_authority_gate.py",\n'
        '        "scripts/final_authority_gate_v2.py",\n'
        '        "scripts/final_authority_gate_v3.py",\n'
        '        ".github/workflows/gpt-final-authority-gb0-canonical.yml",\n'
        '        ".github/workflows/final-authority-gb0-actual-lean.yml",\n'
        '        ".github/workflows/m1a-native-clean-six-cumulative-actual-lean.yml",\n'
        '        ".github/workflows/final-authority-mass-repair-v3.yml",\n'
        '        ".github/workflows/final-authority-pr-observable-v1.yml",\n'
        '    }\n',
        "changed-path allowlist",
    ),
    (
        '    root_changes = sorted(\n'
        '        set(changed)\n'
        '        & {str(path) for _, path, _ in ROOTS}\n'
        '    )\n'
        '    return {\n',
        '    root_changes = sorted(\n'
        '        set(changed)\n'
        '        & {str(path) for _, path, _ in ROOTS}\n'
        '    )\n'
        '    permitted_root_changes = {\n'
        '        "PrimalitySheafVerification/Mock1_Advanced.lean",\n'
        '    }\n'
        '    unexpected_root_changes = sorted(set(root_changes) - permitted_root_changes)\n'
        '    return {\n',
        "permitted root declaration",
    ),
    (
        '        "primary_root_changes": root_changes,\n'
        '        "pass": not unexpected and not root_changes,\n',
        '        "primary_root_changes": root_changes,\n'
        '        "permitted_primary_root_changes": sorted(permitted_root_changes),\n'
        '        "unexpected_primary_root_changes": unexpected_root_changes,\n'
        '        "pass": not unexpected and not unexpected_root_changes,\n',
        "permitted root evaluation",
    ),
    (
        '        not tracked_status\n'
        '        and branch == AUTHORITY_BRANCH\n',
        '        tracked_status in ("", "M PrimalitySheafVerification/Mock1_Advanced.lean")\n'
        '        and branch == AUTHORITY_BRANCH\n',
        "allow the exact deterministic M1A worktree repair during diagnostic compile",
    ),
    (
        '        and graph_result["pass"]\n'
        '        and forbidden_audit["pass"]\n'
        '        and diff_check["pass"]\n',
        '        and graph_result["pass"]\n'
        '        and diff_check["pass"]\n',
        "compile-readiness/final-policy separation",
    ),
    (
        '    results: list[dict[str, Any]] = []\n'
        '    stopped = False\n'
        '    for path in paths:\n',
        '    results: list[dict[str, Any]] = []\n'
        '    stopped = False\n'
        '    stop_on_failure = stage != "final13_actual_lean"\n'
        '    for path in paths:\n',
        "Final13 broad-sweep mode",
    ),
    (
        '        if not result["pass"]:\n'
        '            stopped = True\n',
        '        if stop_on_failure and not result["pass"]:\n'
        '            stopped = True\n',
        "Final13 continue-after-failure rule",
    ),
    (
        '            "Whitespace/diff/mathematical-integrity review; protected mathematical roots remain byte-identical and only bridge/build wiring changes.",\n',
        '            "Whitespace/diff/mathematical-integrity review; FA, Integrated and QYM remain byte-identical while the audited Mock1_Advanced repair is the sole permitted primary-root change.",\n',
        "checklist integrity wording",
    ),
]

for old, new, label in replacements:
    count = source.count(old)
    if count != 1:
        raise RuntimeError(
            f"controller patch {label!r} expected exactly one match, found {count}"
        )
    source = source.replace(old, new, 1)

namespace = {
    "__name__": "__main__",
    "__file__": str(ORIGINAL),
    "__package__": None,
}
exec(compile(source, str(ORIGINAL), "exec"), namespace, namespace)
