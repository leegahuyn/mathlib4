#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path.cwd()
spec = importlib.util.spec_from_file_location(
    "fa459_select", ROOT / "scripts/fa459_select_true_first.py"
)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA459 strict selector")
mod = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mod
spec.loader.exec_module(mod)

mod.BASE = ROOT / "build-logs/fa460-analytic-cluster1"
mod.COLLECTED = mod.BASE / "collected"
mod.SELECTED = mod.BASE / "selected"
mod.PREFIX = "fa460-candidate-"
mod.EXPECTED_VARIANTS = {
    "baseline",
    "macro_cumulative",
    "macro_cluster1_change",
    "macro_cluster1_localEq",
    "postfix_cluster1_change",
    "postfix_cluster1_localEq",
}

if __name__ == "__main__":
    mod.main()
