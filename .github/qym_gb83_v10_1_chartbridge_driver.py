#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import importlib.util
import os

os.environ.setdefault('OUT', '/tmp/qym-gb83-v10-1-chartbridge')
old_path = Path('.github/qym_gb83_v10_normalize4_driver.py')
spec = importlib.util.spec_from_file_location('qym_v10_old_driver', old_path)
if spec is None or spec.loader is None:
    raise SystemExit('cannot load V10 driver')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
old.PATCHER = Path('.github/qym_patch_gb83_v10_1_chartbridge.py')

if __name__ == '__main__':
    raise SystemExit(old.main())
