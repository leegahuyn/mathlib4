#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "scripts" / "fa394_error_window_agent.py"

spec = importlib.util.spec_from_file_location("fa394", WRAPPER)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 394 wrapper")
fa394 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa394)
fa391 = fa394.fa391

TMP_COMPILED = Path("/tmp/fa396-compiled")
shutil.rmtree(TMP_COMPILED, ignore_errors=True)
TMP_COMPILED.mkdir(parents=True, exist_ok=True)


def tmp_output_paths(path: Path, tag: str) -> tuple[Path, Path]:
    safe = path.stem.replace("_", "-")
    base = TMP_COMPILED / f"{safe}-{tag}"
    return Path(str(base) + ".olean"), Path(str(base) + ".ilean")


fa391.output_paths = tmp_output_paths

if __name__ == "__main__":
    raise SystemExit(fa391.main())
