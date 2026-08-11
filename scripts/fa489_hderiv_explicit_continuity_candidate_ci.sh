#!/usr/bin/env bash
set -euo pipefail

export FA488_EVIDENCE_RUN_ID=31456106488
export FA488_EVIDENCE_JOB_ID=93670098634
export FA488_EVIDENCE_HEAD_SHA=ca9f7071476b843379f67765ca43ba7cc327d6be
export FA488_EVIDENCE_SOURCE_SHA256=efabb4d229666d7a6e292e853aa583833ae6c99d0bb6d65689168015eccb93ca
export FA488_FIRST_ERROR_LINE=35337
export FA488_FIRST_ERROR_COL=4
export FA488_FRONTIER_DECLARATION=selectedLogHeightEnergyDensity_continuous
export FA488_FRONTIER_INDEX=2806
export FA489_VARIANT=reuse_local_continuity

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa488_hpoint_typed_by_candidate_ci.sh")
dst = Path("/tmp/fa489_hderiv_explicit_continuity_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa488-hpoint-typed-by", "build-logs/codex-fa489-hderiv-explicit-continuity")
once("scripts/fa488_prepare_hpoint_typed_by.py", "scripts/fa489_prepare_hderiv_explicit_continuity.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa489_hderiv_explicit_continuity_candidate_ci.sh
