#!/usr/bin/env bash
set -euo pipefail

# Exact direct-Lean-observed FA487 provenance.
export FA487_EVIDENCE_RUN_ID=31455433347
export FA487_EVIDENCE_JOB_ID=93668113536
export FA487_EVIDENCE_HEAD_SHA=8a831ead7bd08b53a0d7fe57b76cd34987a56b36
export FA487_EVIDENCE_SOURCE_SHA256=6a478ada53be28bbe1335f440f9663e8a0faaa3576a8b1a602cf7a7330556d03
export FA487_FIRST_ERROR_LINE=35312
export FA487_FIRST_ERROR_COL=11
export FA487_FRONTIER_DECLARATION=selectedLogHeightEnergyDensity_continuous
export FA487_FRONTIER_INDEX=2806
export FA488_VARIANT=typed_by

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa487_hpoint_mk_eq_add_mul_i_candidate_ci.sh")
dst = Path("/tmp/fa488_hpoint_typed_by_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa487-hpoint-mk-eq-add-mul-i", "build-logs/codex-fa488-hpoint-typed-by")
once("scripts/fa487_prepare_hpoint_mk_eq_add_mul_i.py", "scripts/fa488_prepare_hpoint_typed_by.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa488_hpoint_typed_by_candidate_ci.sh
