#!/usr/bin/env bash
set -euo pipefail

export FA498_EVIDENCE_RUN_ID=31467555411
export FA498_EVIDENCE_JOB_ID=93703523832
export FA498_EVIDENCE_HEAD_SHA=199243051aaccaf3ab13c3e1d444b0020758c13f
export FA498_EVIDENCE_SOURCE_SHA256=a4c29aaf4669f99dbdfe7de1c2c4f305bfb7067e8cdc1b08aa3d2a6d6ec9b627
export FA498_FIRST_ERROR_LINE=35657
export FA498_FIRST_ERROR_COL=8
export FA498_FRONTIER_DECLARATION=selectedHeightBasePoint_continuousOn_Ioi
export FA498_FRONTIER_INDEX=2822
export FA499_VARIANT=eta_expand_complex_mk
export FA_COMPILE_MAX_ERRORS="${FA_COMPILE_MAX_ERRORS:-1}"

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa498_height_basepoint_continuouson_type_candidate_ci.sh")
dst = Path("/tmp/fa499_height_basepoint_eta_continuity_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa498-height-basepoint-continuouson-type", "build-logs/codex-fa499-height-basepoint-eta-continuity")
once("scripts/fa498_prepare_height_basepoint_continuouson_type.py", "scripts/fa499_prepare_height_basepoint_eta_continuity.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa499_height_basepoint_eta_continuity_candidate_ci.sh
