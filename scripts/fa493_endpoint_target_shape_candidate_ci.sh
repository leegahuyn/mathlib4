#!/usr/bin/env bash
set -euo pipefail

export FA492_EVIDENCE_RUN_ID=31459132552
export FA492_EVIDENCE_JOB_ID=93678995379
export FA492_EVIDENCE_HEAD_SHA=b4c3fcf295af92271d6dfb180c358632958b14d8
export FA492_EVIDENCE_SOURCE_SHA256=91a277662a1cee06b849445865d8a85331a1cef250c150d5c3f5e4c1b66fe7f7
export FA492_FIRST_ERROR_LINE=35507
export FA492_FIRST_ERROR_COL=44
export FA492_FRONTIER_DECLARATION=norm_selectedCuspCoreTrace_sq_le_logHeightEnergy
export FA492_FRONTIER_INDEX=2812
export FA493_VARIANT=pointwise_change_exact

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa492_endpoint_explicit_continuity_candidate_ci.sh")
dst = Path("/tmp/fa493_endpoint_target_shape_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa492-endpoint-explicit-continuity", "build-logs/codex-fa493-endpoint-target-shape")
once("scripts/fa492_prepare_endpoint_explicit_continuity.py", "scripts/fa493_prepare_endpoint_target_shape.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa493_endpoint_target_shape_candidate_ci.sh
