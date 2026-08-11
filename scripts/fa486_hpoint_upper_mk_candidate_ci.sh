#!/usr/bin/env bash
set -euo pipefail

# Exact direct-Lean-observed FA485 provenance.
export FA485_EVIDENCE_RUN_ID=31453946043
export FA485_EVIDENCE_JOB_ID=93663794188
export FA485_EVIDENCE_HEAD_SHA=c93094fa08fc47dea36fde7dec6f3ab798ae82c6
export FA485_EVIDENCE_SOURCE_SHA256=701d7a7218cb73aeded5090f813487d07f384f38a08b67a0a9518f1dd54ef89a
export FA485_FIRST_ERROR_LINE=35311
export FA485_FIRST_ERROR_COL=10
export FA485_FRONTIER_DECLARATION=selectedLogHeightEnergyDensity_continuous
export FA485_FRONTIER_INDEX=2806
export FA486_VARIANT=explicit_upper_half_plane_mk

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa485_energy_remove_redundant_ring_candidate_ci.sh")
dst = Path("/tmp/fa486_hpoint_upper_mk_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa485-energy-remove-redundant-ring", "build-logs/codex-fa486-hpoint-upper-mk")
once("scripts/fa485_prepare_energy_remove_redundant_ring.py", "scripts/fa486_prepare_hpoint_upper_mk.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa486_hpoint_upper_mk_candidate_ci.sh
