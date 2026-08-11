#!/usr/bin/env bash
set -euo pipefail

export FA495_EVIDENCE_RUN_ID=31464238170
export FA495_EVIDENCE_JOB_ID=93693691898
export FA495_EVIDENCE_HEAD_SHA=a791a5deea1de804049c44cebbc6b5f04fde1032
export FA495_EVIDENCE_SOURCE_SHA256=0cea98064a3970aa66099eec020fc787910584231a7dac68f5e27c71d5aa32bd
export FA495_FIRST_ERROR_LINE=35642
export FA495_FIRST_ERROR_COL=6
export FA495_FRONTIER_DECLARATION=integral_fixedPhaseEuclideanGraphDensity_eq_coordinates
export FA495_FRONTIER_INDEX=2821
export FA496_VARIANT=named_pointwise_integrands

python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa495_orbit_l2_inner_field_candidate_ci.sh')
dst=Path('/tmp/fa496_graph_integral_shape_candidate_ci.sh')
text=src.read_text(encoding='utf-8')
def once(a,b):
    global text
    if text.count(a)!=1: raise RuntimeError(f'expected one {a!r}, got {text.count(a)}')
    text=text.replace(a,b,1)
once('build-logs/codex-fa495-orbit-l2-inner-field','build-logs/codex-fa496-graph-integral-shape')
once('scripts/fa495_prepare_orbit_l2_inner_field.py','scripts/fa496_prepare_graph_integral_shape.py')
dst.write_text(text,encoding='utf-8')
PY
exec bash /tmp/fa496_graph_integral_shape_candidate_ci.sh
