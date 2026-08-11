#!/usr/bin/env bash
set -euo pipefail

export FA499_EVIDENCE_RUN_ID=31468842155
export FA499_EVIDENCE_JOB_ID=93707506552
export FA499_EVIDENCE_HEAD_SHA=2b579f10eac257ba7daa7733674f972a08f88d29
export FA499_EVIDENCE_SOURCE_SHA256=fa2567ec0c2dec43cec56fe0c3df0894c38a61f6f7a65023da7b4efcd941abb1
export FA499_FIRST_ERROR_LINE=35659
export FA499_FIRST_ERROR_COL=2
export FA499_FRONTIER_DECLARATION=selectedHeightBasePoint_continuousOn_Ioi
export FA499_FRONTIER_INDEX=2822
export FA500_VARIANT=explicit_range_witness
export FA_COMPILE_MAX_ERRORS="${FA_COMPILE_MAX_ERRORS:-1}"

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa499_height_basepoint_eta_continuity_candidate_ci.sh")
dst = Path("/tmp/fa500_ofcomplex_source_membership_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa499-height-basepoint-eta-continuity", "build-logs/codex-fa500-ofcomplex-source-membership")
once("scripts/fa499_prepare_height_basepoint_eta_continuity.py", "scripts/fa500_prepare_ofcomplex_source_membership.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa500_ofcomplex_source_membership_candidate_ci.sh
