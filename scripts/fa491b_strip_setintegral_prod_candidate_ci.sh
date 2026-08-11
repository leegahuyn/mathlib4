#!/usr/bin/env bash
set -euo pipefail

export FA490_EVIDENCE_RUN_ID=31457497428
export FA490_EVIDENCE_JOB_ID=93674247669
export FA490_EVIDENCE_HEAD_SHA=8c0c3bfc53b2bdcd7b5b571e4c26852bd0e3a051
export FA490_EVIDENCE_SOURCE_SHA256=e1fd4d4370c14185f81faea26e09b8611bf78e19e583026e55d8ee7adbccd40d
export FA490_FIRST_ERROR_LINE=35483
export FA490_FIRST_ERROR_COL=2
export FA490_FRONTIER_DECLARATION=integral_selectedLogHeightEnergyDensity_stripTail_eq_iterated
export FA490_FRONTIER_INDEX=2811
export FA491B_VARIANT=direct_setIntegral_prod

python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa490_uniform_hlevel_simp_candidate_ci.sh')
dst=Path('/tmp/fa491b_strip_setintegral_prod_candidate_ci.sh')
text=src.read_text(encoding='utf-8')
def once(old,new):
    global text
    c=text.count(old)
    if c != 1: raise RuntimeError(f'expected one {old!r}, found {c}')
    text=text.replace(old,new,1)
once('build-logs/codex-fa490-uniform-hlevel-simp','build-logs/codex-fa491b-strip-setintegral-prod')
once('scripts/fa490_prepare_uniform_hlevel_simp.py','scripts/fa491b_prepare_strip_setintegral_prod.py')
dst.write_text(text,encoding='utf-8')
PY

exec bash /tmp/fa491b_strip_setintegral_prod_candidate_ci.sh
