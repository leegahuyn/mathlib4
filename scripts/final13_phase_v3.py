#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

import final13_phase_v2 as base


def compile_build_all(repo: Path, out: Path) -> dict[str, object]:
    """Compile BuildAll from inside the Lean project root, then remove the source.

    Lean 4.33 rejects an input source located outside the project root.  The v2
    driver generated BuildAll under /tmp, so this wrapper keeps all v2 audits
    and compilation logic but places the temporary source under the canonical
    project tree.  The file is removed in a finally block so pristine-worktree
    and source-identity gates remain meaningful even after a failed compile.
    """

    generated = repo / "PrimalitySheafVerification/BuildAll_Final13_Temporary.lean"
    generated.parent.mkdir(parents=True, exist_ok=True)
    modules = [
        Path(path).with_suffix("").as_posix().replace("/", ".")
        for path in base.ROOTS
    ]
    bridge_module = Path(base.BRIDGE).with_suffix("").as_posix().replace("/", ".")
    imports = [f"import {module}" for module in modules]
    if f"import {bridge_module}" not in imports:
        imports.insert(-1, f"import {bridge_module}")

    source_text = "\n".join(imports) + "\n"
    source_sha256: str | None = None
    olean = out / "generated/BuildAll.olean"
    ilean = out / "generated/BuildAll.ilean"
    try:
        generated.write_text(source_text)
        source_sha256 = base.sha256(generated)
        result = base.run_command(
            [
                "lake",
                "env",
                "lean",
                "-DmaxErrors=10000",
                "-DwarningAsError=false",
                "-o",
                str(olean),
                "-i",
                str(ilean),
                str(generated.relative_to(repo)),
            ],
            out / "logs/BuildAll.log",
            repo,
        )
    finally:
        generated.unlink(missing_ok=True)

    result.update(
        {
            "source": str(generated.relative_to(repo)),
            "source_sha256": source_sha256,
            "source_removed_after_compile": not generated.exists(),
            "olean_exists": olean.is_file() and olean.stat().st_size > 0,
            "ilean_exists": ilean.is_file() and ilean.stat().st_size > 0,
            "imports": imports,
        }
    )
    return result


base.compile_build_all = compile_build_all


if __name__ == "__main__":
    base.main()
