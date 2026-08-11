#!/usr/bin/env bash
set -euo pipefail

: "${FA483_VARIANT:?FA483_VARIANT required}"
: "${FA483_EVIDENCE_RUN_ID:?FA483_EVIDENCE_RUN_ID required}"
: "${FA483_EVIDENCE_JOB_ID:?FA483_EVIDENCE_JOB_ID required}"
: "${FA483_EVIDENCE_HEAD_SHA:?FA483_EVIDENCE_HEAD_SHA required}"
: "${FA483_EVIDENCE_SOURCE_SHA256:?FA483_EVIDENCE_SOURCE_SHA256 required}"
: "${FA483_FIRST_ERROR_LINE:?FA483_FIRST_ERROR_LINE required}"
: "${FA483_FIRST_ERROR_COL:?FA483_FIRST_ERROR_COL required}"
: "${FA483_FRONTIER_DECLARATION:?FA483_FRONTIER_DECLARATION required}"
: "${FA483_FRONTIER_INDEX:?FA483_FRONTIER_INDEX required}"
: "${FA484_VARIANT:?FA484_VARIANT required}"

if [[ "$FA483_VARIANT" != "upper_ext_remove_mk_im" ]]; then
  echo "FA484 requires FA483_VARIANT=upper_ext_remove_mk_im" >&2
  exit 2
fi
if [[ "$FA483_EVIDENCE_RUN_ID" != "31451101943" ]]; then
  echo "FA484 requires FA483 evidence run 31451101943" >&2
  exit 2
fi
if [[ "$FA483_EVIDENCE_JOB_ID" != "93655461634" ]]; then
  echo "FA484 requires FA483 evidence job 93655461634" >&2
  exit 2
fi
if [[ "$FA483_EVIDENCE_HEAD_SHA" != "9ff7ac197487de1f38f63c28d5e52382718738b3" ]]; then
  echo "FA484 requires exact FA483 evidence head" >&2
  exit 2
fi
if [[ "$FA483_EVIDENCE_SOURCE_SHA256" != "34756fc6e6c20dab3d2ff5a125934dde7a065fdee57a9c5b6f2381240ee8481d" ]]; then
  echo "FA484 requires exact FA483 source hash" >&2
  exit 2
fi
if [[ "$FA483_FIRST_ERROR_LINE" != "35255" || "$FA483_FIRST_ERROR_COL" != "37" ]]; then
  echo "FA484 requires FA483 frontier 35255:37" >&2
  exit 2
fi
if [[ "$FA483_FRONTIER_DECLARATION" != "selectedLogHeightEnergyDensity_le_exp_mul_heightGraphDensity" ]]; then
  echo "FA484 requires exact FA483 frontier declaration" >&2
  exit 2
fi
if [[ "$FA483_FRONTIER_INDEX" != "2805" ]]; then
  echo "FA484 requires frontier declaration index 2805" >&2
  exit 2
fi
if [[ "$FA484_VARIANT" != "real_norm_eq_abs_bridge" ]]; then
  echo "unsupported FA484_VARIANT: $FA484_VARIANT" >&2
  exit 2
fi

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa483_selected_height_exp_candidate_ci.sh")
dst = Path("/tmp/fa484_logheight_energy_real_norm_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)

text = replace_once(
    text,
    "build-logs/codex-fa483-selected-height-exp",
    "build-logs/codex-fa484-logheight-energy-real-norm",
)
text = replace_once(
    text,
    "scripts/fa483_prepare_selected_height_exp.py",
    "scripts/fa484_prepare_logheight_energy_real_norm.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa484_logheight_energy_real_norm_candidate_ci.sh
