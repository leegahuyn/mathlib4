#!/usr/bin/env bash
set -euo pipefail

export FA501_EVIDENCE_RUN_ID=31471647828
export FA501_EVIDENCE_JOB_ID=93716072700
export FA501_EVIDENCE_HEAD_SHA=7a5baf0922ecde4b97c77974ceb80e48bf88e094
export FA501_EVIDENCE_SOURCE_SHA256=926ee8186e0a41fda6135a83268c27db9605236674d023b07ab63ae1366a8e7c
export FA501_FIRST_ERROR_LINE=35814
export FA501_FIRST_ERROR_COL=32
export FA501_FRONTIER_DECLARATION=exp_mul_selectedHeightGraphDensity_integrableOn_Ici_log
export FA501_FRONTIER_INDEX=2828
export FA502_VARIANT=pi_zero_apply
export FA_COMPILE_MAX_ERRORS="${FA_COMPILE_MAX_ERRORS:-1}"

python3 - <<'PY'
from pathlib import Path
src = Path('scripts/fa501_height_density_dependent_hlevel_candidate_ci.sh')
dst = Path('/tmp/fa502_exp_density_pi_zero_apply_candidate_ci.sh')
text = src.read_text(encoding='utf-8')
def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'expected one {old!r}, got {count}')
    text = text.replace(old, new, 1)
once('build-logs/codex-fa501-height-density-dependent-hlevel', 'build-logs/codex-fa502-exp-density-pi-zero-apply')
once('scripts/fa501_prepare_height_density_dependent_hlevel.py', 'scripts/fa502_prepare_exp_density_pi_zero_apply.py')
dst.write_text(text, encoding='utf-8')
PY

exec bash /tmp/fa502_exp_density_pi_zero_apply_candidate_ci.sh
