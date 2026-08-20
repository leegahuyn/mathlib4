#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path.cwd()
spec = importlib.util.spec_from_file_location(
    "fa459_select_base", ROOT / "scripts/fa459_select_true_first.py"
)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA459 strict selector")
mod = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mod
spec.loader.exec_module(mod)
mod.PREFIX = "fa459gl-candidate-"
mod.EXPECTED_VARIANTS = {
    "baseline",
    "macro_pair_only",
    "macro_pair_smul",
    "macro_pair_smul_cumulative",
}
if __name__ == "__main__":
    mod.main()
