#!/usr/bin/env bash
set -euo pipefail

export FA492_EVIDENCE_RUN_ID=31459499507
export FA492_EVIDENCE_JOB_ID=93680057199
export FA492_EVIDENCE_HEAD_SHA=76e10532282d2ec9264b11f43ce5ab8a82073065
export FA492_EVIDENCE_SOURCE_SHA256=266bb3bd12fc43826cbbff63297e1ad2b6399c652b54d69e888eeab3344a8856
export FA492_FIRST_ERROR_LINE=35540
export FA492_FIRST_ERROR_COL=2
export FA492_FRONTIER_DECLARATION=fixedPhaseEuclideanGraphDensity_nonneg
export FA492_FRONTIER_INDEX=2814
export FA493_VARIANT=explicit_add_mul_nonneg

python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa492_endpoint_explicit_continuity_candidate_ci.sh')
dst=Path('/tmp/fa493_graph_density_nonneg_candidate_ci.sh')
text=src.read_text()
def once(a,b):
    global text
    if text.count(a)!=1: raise RuntimeError(f'expected one {a!r}, got {text.count(a)}')
    text=text.replace(a,b,1)
once('build-logs/codex-fa492-endpoint-explicit-continuity','build-logs/codex-fa493-graph-density-nonneg')
once('scripts/fa492_prepare_endpoint_explicit_continuity.py','scripts/fa493_prepare_graph_density_nonneg.py')
dst.write_text(text)
PY
exec bash /tmp/fa493_graph_density_nonneg_candidate_ci.sh
