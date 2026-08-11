#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

MODULE_PATH = Path(__file__).with_name("fa_dynamic_apply_staged_library.py")
spec = importlib.util.spec_from_file_location("fa_dynamic_apply_staged_library_base", MODULE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load base staged-library applicator")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def declaration_header(text: str, decl: dict) -> str:
    """Return the immutable declaration header through the first top-level `:=` token.

    The staged FA libraries were authored with header_sha256 computed through `:=`,
    not through `:= by`.  This also covers term-style theorem proofs such as idx3135.
    If a selected declaration has no `:=`, fail closed rather than guessing a body boundary.
    """
    segment = text[decl["start"]:decl["end"]]
    k = segment.find(":=")
    if k < 0:
        raise RuntimeError(
            f"repaired declaration {decl['index']} {decl['name']} has no := terminator"
        )
    return segment[: k + 2]


base.theorem_header = declaration_header


def argument_value(flag: str) -> str:
    try:
        i = sys.argv.index(flag)
    except ValueError as exc:
        raise RuntimeError(f"missing required wrapper argument {flag}") from exc
    if i + 1 >= len(sys.argv):
        raise RuntimeError(f"missing value for {flag}")
    return sys.argv[i + 1]


def main() -> int:
    audit_path = Path(argument_value("--audit-out"))
    target_path = Path(argument_value("--target"))
    result = base.main()
    if result != 0:
        return result
    audit = json.loads(audit_path.read_text(encoding="utf-8"))
    mismatches = []
    for repair in audit.get("proof_replacements_applied", []):
        staged = repair.get("staged_header_sha256")
        current = repair.get("current_header_sha256")
        if staged is not None and staged != current:
            mismatches.append(
                {
                    "declaration_index": repair.get("declaration_index"),
                    "declaration_name": repair.get("declaration_name"),
                    "staged_header_sha256": staged,
                    "current_header_sha256": current,
                }
            )
    audit["strict_staged_header_hash_check"] = {
        "checked": True,
        "mismatches": mismatches,
        "passed": not mismatches,
        "header_boundary": "through-first-:=",
    }
    audit_path.write_text(
        json.dumps(audit, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if mismatches:
        try:
            target_path.unlink()
        except FileNotFoundError:
            pass
        raise RuntimeError("staged declaration header identity mismatch: " + repr(mismatches))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
