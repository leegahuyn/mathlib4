#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa453_selector_ci.sh')
dst=Path('/tmp/fa460_selector_base.sh')
text=src.read_text(encoding='utf-8')
replacements={
    'build-logs/fa453-compact-energy':'build-logs/fa460-analytic-cluster1',
    'python3 scripts/fa442_record_direct_metric.py':'python3 scripts/fa458_record_direct_metric_strict.py',
    'python3 scripts/fa453_select_compact_energy.py':'python3 scripts/fa460_select_cluster1.py',
    "and ind.get('FA_first_actual_error_line')==33929":"and ind.get('FA_first_actual_error_line')==32035",
    "and ind.get('FA_first_actual_error_col')==4":"and ind.get('FA_first_actual_error_col')==79",
    "and ind.get('FA_first_error_declaration')=='compactSupport_height_mul_normSq_le_energy_Ioi'":
        "and ind.get('FA_first_error_declaration')=='nativeActualEdgeFluxIntegral_paired_circular'",
}
for old,new in replacements.items():
    count=text.count(old)
    if count < 1:
        raise SystemExit(f'INFRA_FAILURE: missing selector rewrite {old!r}')
    text=text.replace(old,new)
dst.write_text(text,encoding='utf-8')
PY

exec bash /tmp/fa460_selector_base.sh
