from __future__ import annotations

import shutil
import sys
import tempfile
from pathlib import Path
from typing import Iterable

import fa413_strict_transplant_tournament as core


def scripted_donors(ref: str) -> Iterable[tuple[str, str]]:
    """Materialize only the audited PASS411/PASS412 repair scripts in an isolated worktree.

    The original tournament deliberately never executes repair scripts in the checked-out
    champion tree.  Each donor is generated in a detached temporary worktree and is later
    reduced to a same-height declaration transplant before Lean compilation.
    """
    if "fa411" not in ref and "fa412" not in ref:
        return []
    scripts = core.changed_python_scripts(ref)
    if not scripts:
        return []

    donors: list[tuple[str, str]] = []
    worktree = Path(tempfile.mkdtemp(prefix="fa413-worktree-"))
    try:
        add = core.run(
            ["git", "worktree", "add", "--detach", str(worktree), ref],
            timeout=300,
        )
        if add.returncode != 0:
            return donors
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
        core.run(
            ["git", "worktree", "remove", "--force", str(worktree)],
            timeout=300,
        )
        shutil.rmtree(worktree, ignore_errors=True)
    return donors


core.scripted_donors = scripted_donors

if __name__ == "__main__":
    raise SystemExit(core.main())
