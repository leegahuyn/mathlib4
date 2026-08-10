#!/usr/bin/env python3
from __future__ import annotations

import os
import sys
from pathlib import Path

source = Path('scripts/fa426_run_multiround.py')
text = source.read_text(encoding='utf-8')
old = "common = importlib.util.module_from_spec(spec)\nspec.loader.exec_module(common)\n"
new = "common = importlib.util.module_from_spec(spec)\nimport sys\nsys.modules[spec.name] = common\nspec.loader.exec_module(common)\n"
if text.count(old) != 1:
    raise SystemExit(f'expected one dynamic-import block, found {text.count(old)}')
patched = Path('/tmp/fa426b_run_multiround.py')
patched.write_text(text.replace(old, new), encoding='utf-8')
os.execv(sys.executable, [sys.executable, str(patched)])
