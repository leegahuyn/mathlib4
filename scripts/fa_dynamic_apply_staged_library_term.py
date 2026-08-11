#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

MODULE_PATH = Path(__file__).with_name("fa_dynamic_apply_staged_library.py")
spec = importlib.util.spec_from_file_location("fa_dynamic_apply_staged_library_base", MODULE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load base staged-library applier")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def generalized_header(text: str, decl: dict) -> str:
    """Return the declaration prefix through `:=`, preserving public statement bytes.

    The original helper required `:= by`.  Lean theorems may also use term-style
    proofs (`:= <term>`).  For both forms, the public proposition is exactly the
    prefix before the proof term, so preserving the prefix through `:=` is the
    appropriate semantic firewall.
    """
    segment = text[decl["start"]:decl["end"]]
    k = segment.find(":=")
    if k < 0:
        raise RuntimeError(
            f"repaired declaration {decl['index']} {decl['name']} has no := terminator"
        )
    return segment[: k + 2]


base.theorem_header = generalized_header
raise SystemExit(base.main())
