#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path

source_path = Path(__file__).resolve().parent / 'fa443_confirm_selected.py'
source = source_path.read_text(encoding='utf-8')
source = source.replace(
    "BASELINE_LINE = 31726\nBASELINE_COL = 2\nBASELINE_DECLARATION = \"actualEdgeAmbientParam_hasDerivAt\"",
    "BASELINE_LINE = 32590\nBASELINE_COL = 5\nBASELINE_DECLARATION = \"selectedHalfOpenTile_ae_eq_openTile\"")
source = source.replace(
    "D = ROOT / \"build-logs/fa443-matrix/selected\"",
    "D = ROOT / \"build-logs/fa446-matrix/selected\"")
exec(compile(source, str(source_path), 'exec'), {'__name__': '__main__', '__file__': str(source_path)})
