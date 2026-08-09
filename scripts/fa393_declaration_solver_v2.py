#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import runpy
import sys

ROOT = Path(__file__).resolve().parents[1]
source = ROOT / "scripts" / "fa393_declaration_solver.py"
target = ROOT / "scripts" / ".fa393_declaration_solver_v2_runtime.py"
text = source.read_text(encoding="utf-8")
text = text.replace("import os\n", "import os\nimport sys\n", 1)
old = "H = importlib.util.module_from_spec(spec)\nspec.loader.exec_module(H)"
new = (
    "H = importlib.util.module_from_spec(spec)\n"
    "sys.modules[spec.name] = H\n"
    "spec.loader.exec_module(H)"
)
if text.count(old) != 1:
    raise SystemExit("could not locate dynamic import block exactly")
text = text.replace(old, new, 1)
target.write_text(text, encoding="utf-8")
try:
    sys.argv[0] = str(target)
    runpy.run_path(str(target), run_name="__main__")
finally:
    target.unlink(missing_ok=True)
