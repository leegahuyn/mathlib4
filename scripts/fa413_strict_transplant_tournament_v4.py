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
    temp_root = Path(tempfile.mkdtemp(prefix="fa413-v4-donor-"))
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
        target = worktree / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
        initial = target.read_bytes()
        for script in scripts:
            target.write_bytes(initial)
            proc = core.run([sys.executable, script], cwd=worktree, timeout=180)
            if proc.returncode == 0:
                donors.append((f"{ref}:{script}", target.read_text(encoding="utf-8")))
        target.write_bytes(initial)
        ok = True
        for script in scripts:
            proc = core.run([sys.executable, script], cwd=worktree, timeout=180)
            if proc.returncode != 0:
                ok = False
                break
        if ok:
            donors.append((f"{ref}:cumulative-scripts", target.read_text(encoding="utf-8")))
    finally:
        if added:
            core.run(["git", "worktree", "remove", "--force", str(worktree)], timeout=300)
        shutil.rmtree(temp_root, ignore_errors=True)
    return donors


def _fit_without_semantic_deletion(lines: list[str], height: int) -> list[str] | None:
    fitted = list(lines)
    if len(fitted) <= height:
        return fitted + [""] * (height - len(fitted))

    # Blank lines and single-line comments carry no Lean term.  Removing only these
    # preserves the declaration while keeping every downstream source line fixed.
    removable = [i for i, line in enumerate(fitted) if not line.strip()]
    for i in reversed(removable):
        if len(fitted) <= height:
            break
        del fitted[i]
    removable = [
        i
        for i, line in enumerate(fitted)
        if line.lstrip().startswith("--") and not line.lstrip().startswith("--!")
    ]
    for i in reversed(removable):
        if len(fitted) <= height:
            break
        del fitted[i]
    if len(fitted) > height:
        return None
    return fitted + [""] * (height - len(fitted))


def replace_declaration_same_height(
    base: str,
    base_decl: core.Declaration,
    donor: str,
    donor_decl: core.Declaration,
) -> str | None:
    base_lines = base.splitlines()
    donor_lines = donor.splitlines()[donor_decl.start : donor_decl.end]
    fitted = _fit_without_semantic_deletion(donor_lines, base_decl.lines)
    if fitted is None:
        return None
    if core.header_of(fitted) != base_decl.header:
        return None
    rebuilt = base_lines[: base_decl.start] + fitted + base_lines[base_decl.end :]
    return "\n".join(rebuilt) + ("\n" if base.endswith("\n") else "")


core.scripted_donors = scripted_donors
core.replace_declaration_same_height = replace_declaration_same_height

if __name__ == "__main__":
    raise SystemExit(core.main())
