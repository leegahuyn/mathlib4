#!/usr/bin/env bash
set -euo pipefail

export FA489_EVIDENCE_RUN_ID=31456858385
export FA489_EVIDENCE_JOB_ID=93672410171
export FA489_EVIDENCE_HEAD_SHA=a0b047f5d5894547847966e7e049519b1f9b9edd
export FA489_EVIDENCE_SOURCE_SHA256=365b4489c1a6c60380a40466a50ca338aae5efa14cbdf21fbe97d848bcf540af
export FA489_FIRST_ERROR_LINE=35363
export FA489_FIRST_ERROR_COL=8
export FA489_FRONTIER_DECLARATION=selectedLogHeightNaturalGauge_uniform_eventually_zero
export FA489_FRONTIER_INDEX=2807
export FA490_VARIANT=simp_only_hlevel

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa489_hderiv_explicit_continuity_candidate_ci.sh")
dst = Path("/tmp/fa490_uniform_hlevel_simp_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa489-hderiv-explicit-continuity", "build-logs/codex-fa490-uniform-hlevel-simp")
once("scripts/fa489_prepare_hderiv_explicit_continuity.py", "scripts/fa490_prepare_uniform_hlevel_simp.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa490_uniform_hlevel_simp_candidate_ci.sh
