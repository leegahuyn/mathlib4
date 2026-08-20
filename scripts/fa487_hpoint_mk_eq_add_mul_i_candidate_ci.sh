#!/usr/bin/env bash
set -euo pipefail

# Exact direct-Lean-observed FA486 provenance.
export FA486_EVIDENCE_RUN_ID=31454730748
export FA486_EVIDENCE_JOB_ID=93666070352
export FA486_EVIDENCE_HEAD_SHA=946e1900d0470dc8db26fce4f5590e1302533ca5
export FA486_EVIDENCE_SOURCE_SHA256=22b60d646ff8744f3a59d6d2e35f8698a746b30df1e11a5c4ea0042929decadb
export FA486_FIRST_ERROR_LINE=35312
export FA486_FIRST_ERROR_COL=14
export FA486_FRONTIER_DECLARATION=selectedLogHeightEnergyDensity_continuous
export FA486_FRONTIER_INDEX=2806
export FA487_VARIANT=mk_eq_add_mul_i

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa486_hpoint_upperhalfplanemk_candidate_ci.sh")
dst = Path("/tmp/fa487_hpoint_mk_eq_add_mul_i_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa486-hpoint-upperhalfplanemk", "build-logs/codex-fa487-hpoint-mk-eq-add-mul-i")
once("scripts/fa486_prepare_hpoint_upperhalfplanemk.py", "scripts/fa487_prepare_hpoint_mk_eq_add_mul_i.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa487_hpoint_mk_eq_add_mul_i_candidate_ci.sh
