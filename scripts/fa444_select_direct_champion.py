#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "scripts/fa443_select_direct_champion.py"

spec = importlib.util.spec_from_file_location("fa444_selector_base", BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {BASE}")
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)

# Candidate artifacts are transient inputs.  Never copy the complete matrix
# payload into the repository worktree or stage it in an evidence commit.
module.PREFIX = "fa444-candidate-"
module.COLLECTED = Path("/tmp/fa444-collected")
shutil.rmtree(module.COLLECTED, ignore_errors=True)

if __name__ == "__main__":
    module.main()
