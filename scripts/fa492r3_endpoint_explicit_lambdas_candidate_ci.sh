#!/usr/bin/env bash
set -euo pipefail

export FA492_EVIDENCE_RUN_ID=31459011892
export FA492_EVIDENCE_JOB_ID=93678608893
export FA492_EVIDENCE_HEAD_SHA=2c7cbbc2ba102674d34e713d18098ed9e7ba30d1
export FA492_EVIDENCE_SOURCE_SHA256=91a277662a1cee06b849445865d8a85331a1cef250c150d5c3f5e4c1b66fe7f7
export FA492_FIRST_ERROR_LINE=35507
export FA492_FIRST_ERROR_COL=44
export FA492_FRONTIER_DECLARATION=norm_selectedCuspCoreTrace_sq_le_logHeightEnergy
export FA492_FRONTIER_INDEX=2812

python3 - <<'PY'
from pathlib import Path
src = Path('scripts/fa492_endpoint_explicit_continuity_candidate_ci.sh')
dst = Path('/tmp/fa492r3_endpoint_explicit_lambdas_candidate_ci.sh')
text = src.read_text(encoding='utf-8')
def once(old,new):
    global text
    c=text.count(old)
    if c != 1:
        raise RuntimeError(f'expected one {old!r}, found {c}')
    text=text.replace(old,new,1)
once('build-logs/codex-fa492-endpoint-explicit-continuity','build-logs/codex-fa492r3-endpoint-explicit-lambdas')
once('scripts/fa492_prepare_endpoint_explicit_continuity.py','scripts/fa492r3_prepare_endpoint_explicit_lambdas.py')
dst.write_text(text,encoding='utf-8')
PY

exec bash /tmp/fa492r3_endpoint_explicit_lambdas_candidate_ci.sh
