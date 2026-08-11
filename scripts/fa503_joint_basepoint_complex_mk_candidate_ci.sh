#!/usr/bin/env bash
set -euo pipefail

export FA502_EVIDENCE_RUN_ID=31472717984
export FA502_EVIDENCE_JOB_ID=93719392970
export FA502_EVIDENCE_HEAD_SHA=1bcbb825fa91498278381a0ffc2946cdcbce1f01
export FA502_EVIDENCE_SOURCE_SHA256=db38b9ffb4820e5f7b91816173d635461cd559ff74a36cc69f4c2e5e3034faf3
export FA502_FIRST_ERROR_LINE=35912
export FA502_FIRST_ERROR_COL=8
export FA502_FRONTIER_DECLARATION=selectedHeightBasePoint_joint_continuousOn_positive
export FA502_FRONTIER_INDEX=2831
export FA503_VARIANT=joint_mk_eq_add_mul_i
export FA_COMPILE_MAX_ERRORS="${FA_COMPILE_MAX_ERRORS:-32}"

python3 - <<'PY'
from pathlib import Path
src = Path('scripts/fa502_exp_density_pi_zero_apply_candidate_ci.sh')
dst = Path('/tmp/fa503_joint_basepoint_complex_mk_candidate_ci.sh')
text = src.read_text(encoding='utf-8')
def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'expected one {old!r}, got {count}')
    text = text.replace(old, new, 1)
once('build-logs/codex-fa502-exp-density-pi-zero-apply', 'build-logs/codex-fa503-joint-basepoint-complex-mk')
once('scripts/fa502_prepare_exp_density_pi_zero_apply.py', 'scripts/fa503_prepare_joint_basepoint_complex_mk.py')
dst.write_text(text, encoding='utf-8')
PY

exec bash /tmp/fa503_joint_basepoint_complex_mk_candidate_ci.sh
