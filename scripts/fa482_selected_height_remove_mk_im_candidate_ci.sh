#!/usr/bin/env bash
set -euo pipefail

: "${FA481_VARIANT:?FA481_VARIANT required}"
: "${FA481_EVIDENCE_RUN_ID:?FA481_EVIDENCE_RUN_ID required}"
: "${FA481_EVIDENCE_JOB_ID:?FA481_EVIDENCE_JOB_ID required}"
: "${FA481_EVIDENCE_HEAD_SHA:?FA481_EVIDENCE_HEAD_SHA required}"
: "${FA481_EVIDENCE_SOURCE_SHA256:?FA481_EVIDENCE_SOURCE_SHA256 required}"
: "${FA481_FIRST_ERROR_LINE:?FA481_FIRST_ERROR_LINE required}"
: "${FA481_FIRST_ERROR_COL:?FA481_FIRST_ERROR_COL required}"
: "${FA481_FRONTIER_DECLARATION:?FA481_FRONTIER_DECLARATION required}"
: "${FA481_FRONTIER_INDEX:?FA481_FRONTIER_INDEX required}"
: "${FA482_VARIANT:?FA482_VARIANT required}"

if [[ "$FA481_VARIANT" != "upper_half_plane_ext" ]]; then
  echo "FA482 requires FA481_VARIANT=upper_half_plane_ext" >&2
  exit 2
fi
if [[ "$FA481_EVIDENCE_RUN_ID" != "31420785622" ]]; then
  echo "FA482 requires FA481 evidence run 31420785622" >&2
  exit 2
fi
if [[ "$FA481_EVIDENCE_JOB_ID" != "93560723204" ]]; then
  echo "FA482 requires FA481 evidence job 93560723204" >&2
  exit 2
fi
if [[ "$FA481_EVIDENCE_HEAD_SHA" != "058fe008a54c3fc1b170a27320a41eb942a1d409" ]]; then
  echo "FA482 requires exact FA481 evidence head" >&2
  exit 2
fi
if [[ "$FA481_EVIDENCE_SOURCE_SHA256" != "bf1f5f64a53662e9c583e8af37aef603d0b96119a6623f029979ceda1a721614" ]]; then
  echo "FA482 requires exact FA481 source hash" >&2
  exit 2
fi
if [[ "$FA481_FIRST_ERROR_LINE" != "35198" || "$FA481_FIRST_ERROR_COL" != "46" ]]; then
  echo "FA482 requires FA481 frontier 35198:46" >&2
  exit 2
fi
if [[ "$FA481_FRONTIER_DECLARATION" != "selectedHeightBasePoint_of_pos" ]]; then
  echo "FA482 requires frontier declaration selectedHeightBasePoint_of_pos" >&2
  exit 2
fi
if [[ "$FA481_FRONTIER_INDEX" != "2802" ]]; then
  echo "FA482 requires frontier declaration index 2802" >&2
  exit 2
fi
if [[ "$FA482_VARIANT" != "remove_complex_mk_im" ]]; then
  echo "unsupported FA482_VARIANT: $FA482_VARIANT" >&2
  exit 2
fi

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa481_selected_height_basepoint_candidate_ci.sh")
dst = Path("/tmp/fa482_selected_height_remove_mk_im_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)

text = replace_once(
    text,
    "build-logs/codex-fa481-selected-height-basepoint",
    "build-logs/codex-fa482-selected-height-remove-mk-im",
)
text = replace_once(
    text,
    "scripts/fa481_prepare_selected_height_basepoint.py",
    "scripts/fa482_prepare_selected_height_remove_mk_im.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa482_selected_height_remove_mk_im_candidate_ci.sh
