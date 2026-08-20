#!/usr/bin/env bash
set -euo pipefail

export FA490_EVIDENCE_RUN_ID=31457486168
export FA490_EVIDENCE_JOB_ID=93674214588
export FA490_EVIDENCE_HEAD_SHA=0fd0bc8c28cda9959fe1389359db600091f3bf99
export FA490_EVIDENCE_SOURCE_SHA256=e1fd4d4370c14185f81faea26e09b8611bf78e19e583026e55d8ee7adbccd40d
export FA490_FIRST_ERROR_LINE=35483
export FA490_FIRST_ERROR_COL=2
export FA490_FRONTIER_DECLARATION=integral_selectedLogHeightEnergyDensity_stripTail_eq_iterated
export FA490_FRONTIER_INDEX=2811
export FA491_VARIANT=rewrite_prod_restrict_then_fubini

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa490_uniform_hlevel_simp_candidate_ci.sh")
dst = Path("/tmp/fa491_strip_fubini_prod_restrict_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa490-uniform-hlevel-simp", "build-logs/codex-fa491-strip-fubini-prod-restrict")
once("scripts/fa490_prepare_uniform_hlevel_simp.py", "scripts/fa491_prepare_strip_fubini_prod_restrict.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa491_strip_fubini_prod_restrict_candidate_ci.sh
