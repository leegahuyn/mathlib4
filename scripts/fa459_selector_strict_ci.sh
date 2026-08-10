#!/usr/bin/env bash
set -euo pipefail

# Reuse the mature FA453 checked-in materialization/x2/downstream gate, but
# replace every stale first-error assumption with the strict categorized
# diagnostic authority discovered by FA457/FA458.
python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa453_selector_ci.sh')
dst=Path('/tmp/fa459_selector_base.sh')
text=src.read_text(encoding='utf-8')
replacements={
    'python3 scripts/fa442_record_direct_metric.py':
        'python3 scripts/fa458_record_direct_metric_strict.py',
    'python3 scripts/fa453_select_compact_energy.py':
        'python3 scripts/fa459_select_true_first.py',
    "and ind.get('FA_first_actual_error_line')==33929":
        "and ind.get('FA_first_actual_error_line')==32035",
    "and ind.get('FA_first_actual_error_col')==4":
        "and ind.get('FA_first_actual_error_col')==79",
    "and ind.get('FA_first_error_declaration')=='compactSupport_height_mul_normSq_le_energy_Ioi'":
        "and ind.get('FA_first_error_declaration')=='nativeActualEdgeFluxIntegral_paired_circular'",
}
for old,new in replacements.items():
    count=text.count(old)
    if count != 1:
        raise SystemExit(f'INFRA_FAILURE: selector patch expected one {old!r}, found {count}')
    text=text.replace(old,new,1)
# Make the evidence/report labels truthful about the strict baseline generation.
text=text.replace('FA453', 'FA459')
text=text.replace('FA451 champion', 'strict categorized FA451-source baseline')
text=text.replace('compact-energy', 'strict-true-first')
dst.write_text(text,encoding='utf-8')
PY

exec bash /tmp/fa459_selector_base.sh
