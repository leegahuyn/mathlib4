#!/usr/bin/env bash
set -euo pipefail
export FA491_EVIDENCE_RUN_ID=31458257120
export FA491_EVIDENCE_JOB_ID=93676458948
export FA491_EVIDENCE_HEAD_SHA=d030aecf662d3f8ff36d5d0776a7ddc93f4c1e70
export FA491_EVIDENCE_SOURCE_SHA256=ccea869bcd941660cf537806e8ce53a8af242685751bc81e16ff4a6256a8023d
export FA491_FIRST_ERROR_LINE=35507
export FA491_FIRST_ERROR_COL=6
export FA491_FRONTIER_DECLARATION=norm_selectedCuspCoreTrace_sq_le_logHeightEnergy
export FA491_FRONTIER_INDEX=2812
export FA492B_VARIANT=explicit_rw_hpoint
python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa491_strip_fubini_prod_restrict_candidate_ci.sh'); dst=Path('/tmp/fa492b_endpoint_explicit_rw_candidate_ci.sh'); text=src.read_text(encoding='utf-8')
def once(old,new):
 global text
 c=text.count(old)
 if c!=1: raise RuntimeError(f'expected one {old!r}, found {c}')
 text=text.replace(old,new,1)
once('build-logs/codex-fa491-strip-fubini-prod-restrict','build-logs/codex-fa492b-endpoint-explicit-rw')
once('scripts/fa491_prepare_strip_fubini_prod_restrict.py','scripts/fa492b_prepare_endpoint_explicit_rw.py')
dst.write_text(text,encoding='utf-8')
PY
exec bash /tmp/fa492b_endpoint_explicit_rw_candidate_ci.sh
