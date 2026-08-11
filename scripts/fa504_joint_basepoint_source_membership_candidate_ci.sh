#!/usr/bin/env bash
set -euo pipefail

export FA503_EVIDENCE_RUN_ID=31475061266
export FA503_EVIDENCE_JOB_ID=93726750556
export FA503_EVIDENCE_HEAD_SHA=60d9820e64ab5ef3f14abc7cfbd0c1f2b1d4a522
export FA503_EVIDENCE_SOURCE_SHA256=46d208e7893993190355c092623882dd3df8c4e36b9df3d21a0b28db1a583a2f
export FA503_FIRST_ERROR_LINE=35917
export FA503_FIRST_ERROR_COL=2
export FA503_FRONTIER_DECLARATION=selectedHeightBasePoint_joint_continuousOn_positive
export FA503_FRONTIER_INDEX=2831
export FA504_VARIANT=explicit_range_witness
export FA_COMPILE_MAX_ERRORS="${FA_COMPILE_MAX_ERRORS:-32}"

python3 - <<'PY'
from pathlib import Path
src = Path('scripts/fa503_joint_basepoint_complex_mk_candidate_ci.sh')
dst = Path('/tmp/fa504_joint_basepoint_source_membership_candidate_ci.sh')
text = src.read_text(encoding='utf-8')
def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'expected one {old!r}, got {count}')
    text = text.replace(old, new, 1)
once('build-logs/codex-fa503-joint-basepoint-complex-mk', 'build-logs/codex-fa504-joint-basepoint-source-membership')
once('scripts/fa503_prepare_joint_basepoint_complex_mk.py', 'scripts/fa504_prepare_joint_basepoint_source_membership.py')
dst.write_text(text, encoding='utf-8')
PY

exec bash /tmp/fa504_joint_basepoint_source_membership_candidate_ci.sh
