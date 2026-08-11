#!/usr/bin/env bash
set -euo pipefail

: "${FA484_VARIANT:?FA484_VARIANT required}"
: "${FA484_EVIDENCE_RUN_ID:?FA484_EVIDENCE_RUN_ID required}"
: "${FA484_EVIDENCE_JOB_ID:?FA484_EVIDENCE_JOB_ID required}"
: "${FA484_EVIDENCE_HEAD_SHA:?FA484_EVIDENCE_HEAD_SHA required}"
: "${FA484_EVIDENCE_SOURCE_SHA256:?FA484_EVIDENCE_SOURCE_SHA256 required}"
: "${FA484_FIRST_ERROR_LINE:?FA484_FIRST_ERROR_LINE required}"
: "${FA484_FIRST_ERROR_COL:?FA484_FIRST_ERROR_COL required}"
: "${FA484_FRONTIER_DECLARATION:?FA484_FRONTIER_DECLARATION required}"
: "${FA484_FRONTIER_INDEX:?FA484_FRONTIER_INDEX required}"
: "${FA485_VARIANT:?FA485_VARIANT required}"

[[ "$FA484_VARIANT" == "real_norm_eq_abs_bridge" ]]
[[ "$FA484_EVIDENCE_RUN_ID" == "31451815080" ]]
[[ "$FA484_EVIDENCE_JOB_ID" == "93657549435" ]]
[[ "$FA484_EVIDENCE_HEAD_SHA" == "5553ea94b57f065f578569b6a75daf184c18b841" ]]
[[ "$FA484_EVIDENCE_SOURCE_SHA256" == "c4a4dc3bac0d11381071fd11513b175f8eb5f93037e27ed3622bba1a2df26eb6" ]]
[[ "$FA484_FIRST_ERROR_LINE" == "35280" && "$FA484_FIRST_ERROR_COL" == "8" ]]
[[ "$FA484_FRONTIER_DECLARATION" == "selectedLogHeightEnergyDensity_le_exp_mul_heightGraphDensity" ]]
[[ "$FA484_FRONTIER_INDEX" == "2805" ]]
[[ "$FA485_VARIANT" == "neutralize_redundant_ring" ]]

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa484_logheight_energy_real_norm_candidate_ci.sh")
dst = Path("/tmp/fa485_remove_redundant_ring_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa484-logheight-energy-real-norm", "build-logs/codex-fa485-remove-redundant-ring")
once("scripts/fa484_prepare_logheight_energy_real_norm.py", "scripts/fa485_prepare_remove_redundant_ring.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa485_remove_redundant_ring_candidate_ci.sh
