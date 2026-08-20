#!/usr/bin/env bash
set -euo pipefail

export FA494_EVIDENCE_RUN_ID=31463480421
export FA494_EVIDENCE_JOB_ID=93691559188
export FA494_EVIDENCE_HEAD_SHA=d6c811a4419b75fb0494e14e1095d5c036ed53ae
export FA494_EVIDENCE_SOURCE_SHA256=0c12385bb59897283b26f5e0065dcee042d784b4e16013f54d34808c7b562328
export FA494_FIRST_ERROR_LINE=35577
export FA494_FIRST_ERROR_COL=8
export FA494_FRONTIER_DECLARATION=orbitEuclideanL2_norm_sq_eq_integral
export FA494_FRONTIER_INDEX=2817
export FA495_VARIANT=complex_scalar_field

python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa494_height_graph_zeta_rewrite_candidate_ci.sh')
dst=Path('/tmp/fa495_orbit_l2_inner_field_candidate_ci.sh')
text=src.read_text(encoding='utf-8')
def once(a,b):
    global text
    if text.count(a)!=1: raise RuntimeError(f'expected one {a!r}, got {text.count(a)}')
    text=text.replace(a,b,1)
once('build-logs/codex-fa494-height-graph-zeta-rewrite','build-logs/codex-fa495-orbit-l2-inner-field')
once('scripts/fa494_prepare_height_graph_zeta_rewrite.py','scripts/fa495_prepare_orbit_l2_inner_field.py')
dst.write_text(text,encoding='utf-8')
PY
exec bash /tmp/fa495_orbit_l2_inner_field_candidate_ci.sh
