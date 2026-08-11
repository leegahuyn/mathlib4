#!/usr/bin/env bash
set -euo pipefail

export FA496_EVIDENCE_RUN_ID=31465439549
export FA496_EVIDENCE_JOB_ID=93697278510
export FA496_EVIDENCE_HEAD_SHA=50758d199b5db689e08d78057cc40281cceb9262
export FA496_EVIDENCE_SOURCE_SHA256=8556a6ccc3eef48d13e359ab3e29488dfa36442ed90e0fbc6509c8772b16b12d
export FA496_FIRST_ERROR_LINE=35657
export FA496_FIRST_ERROR_COL=8
export FA496_FRONTIER_DECLARATION=selectedHeightBasePoint_continuousOn_Ioi
export FA496_FRONTIER_INDEX=2822
export FA497_VARIANT=mk_eq_add_mul_i_continuous_on

python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa496_graph_integral_shape_candidate_ci.sh')
dst=Path('/tmp/fa497_height_basepoint_mk_continuity_candidate_ci.sh')
text=src.read_text(encoding='utf-8')
def once(a,b):
    global text
    if text.count(a)!=1:
        raise RuntimeError(f'expected one {a!r}, got {text.count(a)}')
    text=text.replace(a,b,1)
once('build-logs/codex-fa496-graph-integral-shape','build-logs/codex-fa497-height-basepoint-mk-continuity')
once('scripts/fa496_prepare_graph_integral_shape.py','scripts/fa497_prepare_height_basepoint_mk_continuity.py')
dst.write_text(text,encoding='utf-8')
PY
exec bash /tmp/fa497_height_basepoint_mk_continuity_candidate_ci.sh
