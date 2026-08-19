#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import importlib.util
import os

os.environ.setdefault('OUT', '/tmp/qym-v11-edgeparametertransport')
old_path = Path('.github/qym_v11_edgeparametertransport_driver.py')
spec = importlib.util.spec_from_file_location('qym_v11_driver_base', old_path)
if spec is None or spec.loader is None:
    raise SystemExit('cannot load V11 base driver')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
old.VARIANTS = ('letI_change', 'letI_simpa', 'transparent_simpa')

if __name__ == '__main__':
    raise SystemExit(old.main())
