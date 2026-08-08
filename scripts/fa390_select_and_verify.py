from __future__ import annotations

import importlib.util
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE_PATH = ROOT / "scripts" / "fa383_select_and_verify.py"

spec = importlib.util.spec_from_file_location("fa383_select_verify_extended", BASE_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot import {BASE_PATH}")
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)

_original_repair_module = base.repair_module


def extended_repair_module(path, evidence, max_frontiers=10):
    configured = int(os.environ.get("FA390_DOWNSTREAM_FRONTIERS", "24"))
    return _original_repair_module(path, evidence, max_frontiers=max(configured, max_frontiers))


base.repair_module = extended_repair_module

if __name__ == "__main__":
    raise SystemExit(base.main())
