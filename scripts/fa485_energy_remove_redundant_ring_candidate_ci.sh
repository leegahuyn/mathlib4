#!/usr/bin/env bash
set -euo pipefail

# Exact direct-Lean-observed FA484 provenance.
export FA484_EVIDENCE_RUN_ID=31452464855
export FA484_EVIDENCE_JOB_ID=93659399923
export FA484_EVIDENCE_HEAD_SHA=88c7e42f85022181be319af9f1be1d8f0c00ccec
export FA484_EVIDENCE_SOURCE_SHA256=c4a4dc3bac0d11381071fd11513b175f8eb5f93037e27ed3622bba1a2df26eb6
export FA484_FIRST_ERROR_LINE=35280
export FA484_FIRST_ERROR_COL=8
export FA484_FRONTIER_DECLARATION=selectedLogHeightEnergyDensity_le_exp_mul_heightGraphDensity
export FA484_FRONTIER_INDEX=2805
export FA485_VARIANT=remove_redundant_ring

python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa484_energy_real_norm_abs_candidate_ci.sh")
dst = Path("/tmp/fa485_energy_remove_redundant_ring_candidate_ci.sh")
text = src.read_text(encoding="utf-8")

def once(old: str, new: str):
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    text = text.replace(old, new, 1)

once("build-logs/codex-fa484-energy-real-norm-abs", "build-logs/codex-fa485-energy-remove-redundant-ring")
once("scripts/fa484_prepare_energy_real_norm_abs.py", "scripts/fa485_prepare_energy_remove_redundant_ring.py")
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa485_energy_remove_redundant_ring_candidate_ci.sh
