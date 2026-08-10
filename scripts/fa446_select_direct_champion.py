#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'scripts/fa443_select_direct_champion.py'
spec = importlib.util.spec_from_file_location('fa446_selector_base', BASE)
if spec is None or spec.loader is None:
    raise RuntimeError(f'cannot load {BASE}')
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
module.BASELINE_SHA = '4647a9463e4264a7f0e08405b7ccd1ce9be87e7227fa2b91dc52024e2e198152'
module.BASELINE_LINE = 32590
module.BASELINE_COL = 5
module.BASELINE_DECLARATION = 'selectedHalfOpenTile_ae_eq_openTile'
module.EXPECTED_VARIANTS = [
    'baseline',
    'measurable_only',
    'measurable_height',
    'measurable_height_upper',
    'measurable_height_upper_pointwise',
    'measurable_height_upper_pointwise_memspace',
    'measurable_height_upper_pointwise_memspace_lp',
    'measurable_height_upper_pointwise_memspace_lp_tail',
    'measurable_height_upper_pointwise_memspace_lp_tail_zero',
]
module.PREFIX = 'fa446-candidate-'
module.COLLECTED = Path('/tmp/fa446-collected')
module.SELECTED = ROOT / 'build-logs/fa446-matrix/selected'
shutil.rmtree(module.COLLECTED, ignore_errors=True)

if __name__ == '__main__':
    module.main()
