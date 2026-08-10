#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path.cwd()
spec = importlib.util.spec_from_file_location(
    "fa460_prepare_v1", ROOT / "scripts/fa460_prepare_analytic_cluster1.py"
)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA460 cluster1 preparer")
mod = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mod
spec.loader.exec_module(mod)

_original_replace_once = mod.replace_once


def corrected_replace_once(text: str, old: str, new: str, label: str) -> str:
    if label == "unfold unitary pullback before dx_mul":
        old = "dy f (selectedCosetAction q z)) := by\n  rw [dx_mul"
        new = (
            "dy f (selectedCosetAction q z)) := by\n"
            "  unfold selectedCosetUnitaryPullback\n"
            "  rw [dx_mul"
        )
    elif label == "unfold unitary pullback before dy_mul":
        old = "dy f (selectedCosetAction q z)) := by\n  rw [dy_mul"
        new = (
            "dy f (selectedCosetAction q z)) := by\n"
            "  unfold selectedCosetUnitaryPullback\n"
            "  rw [dy_mul"
        )
    return _original_replace_once(text, old, new, label)


mod.replace_once = corrected_replace_once

if __name__ == "__main__":
    mod.main()
