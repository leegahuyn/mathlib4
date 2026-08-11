#!/usr/bin/env bash
set -euo pipefail

: "${FA485_VARIANT:?FA485_VARIANT required}"
: "${FA485_EVIDENCE_RUN_ID:?FA485_EVIDENCE_RUN_ID required}"
: "${FA485_EVIDENCE_JOB_ID:?FA485_EVIDENCE_JOB_ID required}"
: "${FA485_EVIDENCE_HEAD_SHA:?FA485_EVIDENCE_HEAD_SHA required}"
: "${FA485_EVIDENCE_SOURCE_SHA256:?FA485_EVIDENCE_SOURCE_SHA256 required}"
: "${FA485_FIRST_ERROR_LINE:?FA485_FIRST_ERROR_LINE required}"
: "${FA485_FIRST_ERROR_COL:?FA485_FIRST_ERROR_COL required}"
: "${FA485_FRONTIER_DECLARATION:?FA485_FRONTIER_DECLARATION required}"
: "${FA485_FRONTIER_INDEX:?FA485_FRONTIER_INDEX required}"
: "${FA486_VARIANT:?FA486_VARIANT required}"

[[ "$FA485_VARIANT" == "neutralize_redundant_ring" ]]
[[ "$FA485_EVIDENCE_RUN_ID" == "31452647851" ]]
[[ "$FA485_EVIDENCE_JOB_ID" == "93660105937" ]]
[[ "$FA485_EVIDENCE_HEAD_SHA" == "812df4c1d0232c12c3567a05a7d9b9ada8ca56a8" ]]
[[ "$FA485_EVIDENCE_SOURCE_SHA256" == "8e5732de22dff5e1c293c824d4696df8b6937e9f2625713b7c3a424286fde76e" ]]
[[ "$FA485_FIRST_ERROR_LINE" == "35311" && "$FA485_FIRST_ERROR_COL" == "10" ]]
[[ "$FA485_FRONTIER_DECLARATION" == "selectedLogHeightEnergyDensity_continuous" ]]
[[ "$FA485_FRONTIER_INDEX" == "2806" ]]
[[ "$FA486_VARIANT" == "direct_fun_prop" ]]

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa485_remove_redundant_ring_candidate_ci.sh")
dst = Path("/tmp/fa486_hpoint_fun_prop_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa485-remove-redundant-ring", "build-logs/codex-fa486-hpoint-fun-prop")
once("scripts/fa485_prepare_remove_redundant_ring.py", "scripts/fa486_prepare_hpoint_fun_prop.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa486_hpoint_fun_prop_candidate_ci.sh
