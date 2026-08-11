#!/usr/bin/env bash
set -euo pipefail

export FA491_EVIDENCE_RUN_ID=31458337236
export FA491_EVIDENCE_JOB_ID=93676647064
export FA491_EVIDENCE_HEAD_SHA=744880346f214b5ae3aa975f5c529edd29b42bd3
export FA491_EVIDENCE_SOURCE_SHA256=ccea869bcd941660cf537806e8ce53a8af242685751bc81e16ff4a6256a8023d
export FA491_FIRST_ERROR_LINE=35507
export FA491_FIRST_ERROR_COL=6
export FA491_FRONTIER_DECLARATION=norm_selectedCuspCoreTrace_sq_le_logHeightEnergy
export FA491_FRONTIER_INDEX=2812
export FA492_VARIANT=reuse_hh_endpoint

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa491_strip_fubini_prod_restrict_candidate_ci.sh")
dst = Path("/tmp/fa492_endpoint_explicit_continuity_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa491-strip-fubini-prod-restrict", "build-logs/codex-fa492-endpoint-explicit-continuity")
once("scripts/fa491_prepare_strip_fubini_prod_restrict.py", "scripts/fa492_prepare_endpoint_explicit_continuity.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa492_endpoint_explicit_continuity_candidate_ci.sh
