#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / "scripts" / "fa394_error_window_agent.py"

spec = importlib.util.spec_from_file_location("fa394", WRAPPER)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load PASS 394 error-window wrapper")
fa394 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa394)
fa391 = fa394.fa391

TMP_COMPILED = Path("/tmp/fa397-candidates")
shutil.rmtree(TMP_COMPILED, ignore_errors=True)
TMP_COMPILED.mkdir(parents=True, exist_ok=True)


def dependency_aware_output_paths(path: Path, tag: str) -> tuple[Path, Path]:
    """Keep speculative candidates outside the repository, but write accepted
    two-pass verification artifacts to Mathlib's canonical project build path.

    The canonical verify artifacts are required so the next target in the strict
    order can import the exact just-verified predecessor rather than a stale or
    missing `.olean`.
    """
    if tag.startswith("verify-"):
        module = path.relative_to(ROOT).with_suffix("")
        base = ROOT / ".lake" / "build" / "lib" / "lean" / module
        base.parent.mkdir(parents=True, exist_ok=True)
        return Path(str(base) + ".olean"), Path(str(base) + ".ilean")

    safe = path.stem.replace("_", "-")
    base = TMP_COMPILED / f"{safe}-{tag}"
    return Path(str(base) + ".olean"), Path(str(base) + ".ilean")


fa391.output_paths = dependency_aware_output_paths

if __name__ == "__main__":
    raise SystemExit(fa391.main())
