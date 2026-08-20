#!/usr/bin/env bash
set -euo pipefail

export FA493_EVIDENCE_RUN_ID=31460205923
export FA493_EVIDENCE_JOB_ID=93682055075
export FA493_EVIDENCE_HEAD_SHA=7611dae00b47dbac9801744c4f4c821eca8dd9c0
export FA493_EVIDENCE_SOURCE_SHA256=8a0be67731e5cc1314b0ff81829a73b6845612bdf14fa51a648c4442378d3ee9
export FA493_FIRST_ERROR_LINE=35567
export FA493_FIRST_ERROR_COL=6
export FA493_FRONTIER_DECLARATION=selectedHeightGraphDensity_eq_scale_mul_fixedPhaseDensity
export FA493_FRONTIER_INDEX=2816
export FA494_VARIANT=zeta_then_rewrite

python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa493_graph_density_nonneg_candidate_ci.sh')
dst=Path('/tmp/fa494_height_graph_zeta_rewrite_candidate_ci.sh')
text=src.read_text(encoding='utf-8')
def once(a,b):
    global text
    if text.count(a)!=1: raise RuntimeError(f'expected one {a!r}, got {text.count(a)}')
    text=text.replace(a,b,1)
once('build-logs/codex-fa493-graph-density-nonneg','build-logs/codex-fa494-height-graph-zeta-rewrite')
once('scripts/fa493_prepare_graph_density_nonneg.py','scripts/fa494_prepare_height_graph_zeta_rewrite.py')
dst.write_text(text,encoding='utf-8')
PY
exec bash /tmp/fa494_height_graph_zeta_rewrite_candidate_ci.sh
