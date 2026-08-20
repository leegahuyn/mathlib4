#!/usr/bin/env python3
"""Repository-exact SHA lock for the Candidate05 dynamic patch."""
from __future__ import annotations

import importlib.util
from pathlib import Path

MODULE_PATH = Path(__file__).with_name("gpt_fa_primary4016_candidate05_patch.py")
spec = importlib.util.spec_from_file_location("gpt_candidate05_patch_base", MODULE_PATH)
if spec is None or spec.loader is None:
    raise SystemExit("failed to load Candidate05 base patch module")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
module.EXPECTED_OUTPUT = "6ff74433b057db1ad0cb877771688c28bf597fd6c447e38e1e7fa80886495bbf"
module.main()
