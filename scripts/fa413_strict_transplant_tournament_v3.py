from __future__ import annotations

import shutil
import sys
import tempfile
from pathlib import Path
from typing import Iterable

import fa413_strict_transplant_tournament as core


def scripted_donors(ref: str) -> Iterable[tuple[str, str]]:
    if "fa411" not in ref and "fa412" not in ref:
        return []
    scripts = core.changed_python_scripts(ref)
    if not scripts:
        return []

    donors: list[tuple[str, str]] = []
    temp_root = Path(tempfile.mkdtemp(prefix="fa413-donor-root-"))
    worktree = temp_root / "worktree"
    added = False
    try:
        add = core.run(
            ["git", "worktree", "add", "--detach", str(worktree), ref],
            timeout=300,
        )
        if add.returncode != 0:
            return donors
        added = True
        donor_target = (
            worktree
            / "PrimalitySheafVerification"
            / "Mock2_FunctionalAnalysis.lean"
        )
        initial = donor_target.read_bytes()

        for script in scripts:
            donor_target.write_bytes(initial)
            proc = core.run([sys.executable, script], cwd=worktree, timeout=180)
            if proc.returncode == 0 and donor_target.exists():
                donors.append(
                    (f"{ref}:{script}", donor_target.read_text(encoding="utf-8"))
                )

        donor_target.write_bytes(initial)
        cumulative_ok = True
        for script in scripts:
            proc = core.run([sys.executable, script], cwd=worktree, timeout=180)
            if proc.returncode != 0:
                cumulative_ok = False
                break
        if cumulative_ok:
            donors.append(
                (
                    f"{ref}:cumulative-scripts",
                    donor_target.read_text(encoding="utf-8"),
                )
            )
    finally:
        if added:
            core.run(
                ["git", "worktree", "remove", "--force", str(worktree)],
                timeout=300,
            )
        shutil.rmtree(temp_root, ignore_errors=True)
    return donors


core.scripted_donors = scripted_donors

if __name__ == "__main__":
    raise SystemExit(core.main())
