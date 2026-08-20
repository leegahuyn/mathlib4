#!/usr/bin/env bash
set -euo pipefail

export FA497_EVIDENCE_RUN_ID=31466476355
export FA497_EVIDENCE_JOB_ID=93700363537
export FA497_EVIDENCE_HEAD_SHA=f27916a15c00f57e48908d4abcdbc40a2974d2d3
export FA497_EVIDENCE_SOURCE_SHA256=3c0d028cb84458ba243e8debde0b9067744570a81b08bfb5cf4414b9efede7c3
export FA497_FIRST_ERROR_LINE=35657
export FA497_FIRST_ERROR_COL=8
export FA497_FRONTIER_DECLARATION=selectedHeightBasePoint_continuousOn_Ioi
export FA497_FRONTIER_INDEX=2822
export FA498_VARIANT=typed_continuous_on_set

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa497_height_basepoint_mk_continuity_candidate_ci.sh")
dst = Path("/tmp/fa498_height_basepoint_continuouson_type_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa497-height-basepoint-mk-continuity", "build-logs/codex-fa498-height-basepoint-continuouson-type")
once("scripts/fa497_prepare_height_basepoint_mk_continuity.py", "scripts/fa498_prepare_height_basepoint_continuouson_type.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa498_height_basepoint_continuouson_type_candidate_ci.sh
