#!/usr/bin/env bash
set -euo pipefail

: "${HORIZONTAL_STYLE:?HORIZONTAL_STYLE required}"
: "${VARIANT:?VARIANT required}"
: "${FA473_WINNER:?FA473_WINNER required}"
: "${FA474_WINNER:?FA474_WINNER required}"
: "${FA475_WINNER:?FA475_WINNER required}"
: "${FA476_R2_VARIANT:?FA476_R2_VARIANT required}"
: "${FA476_R3_VARIANT:?FA476_R3_VARIANT required}"
: "${FA476_R3_EVIDENCE_RUN_ID:?FA476_R3_EVIDENCE_RUN_ID required}"
: "${FA476_R3_EVIDENCE_ARTIFACT_ID:?FA476_R3_EVIDENCE_ARTIFACT_ID required}"
: "${FA476_R3_EVIDENCE_ARTIFACT_DIGEST:?FA476_R3_EVIDENCE_ARTIFACT_DIGEST required}"
: "${FA477_VARIANT:?FA477_VARIANT required}"
: "${FA477_EVIDENCE_RUN_ID:?FA477_EVIDENCE_RUN_ID required}"
: "${FA477_EVIDENCE_JOB_ID:?FA477_EVIDENCE_JOB_ID required}"
: "${FA477_EVIDENCE_HEAD_SHA:?FA477_EVIDENCE_HEAD_SHA required}"
: "${FA477_EVIDENCE_ARTIFACT_ID:?FA477_EVIDENCE_ARTIFACT_ID required}"
: "${FA477_EVIDENCE_ARTIFACT_NAME:?FA477_EVIDENCE_ARTIFACT_NAME required}"
: "${FA477_EVIDENCE_ARTIFACT_SIZE:?FA477_EVIDENCE_ARTIFACT_SIZE required}"
: "${FA477_EVIDENCE_ARTIFACT_DIGEST:?FA477_EVIDENCE_ARTIFACT_DIGEST required}"
: "${FA478_VARIANT:?FA478_VARIANT required}"
: "${FA478_EVIDENCE_RUN_ID:?FA478_EVIDENCE_RUN_ID required}"
: "${FA478_EVIDENCE_JOB_ID:?FA478_EVIDENCE_JOB_ID required}"
: "${FA478_EVIDENCE_HEAD_SHA:?FA478_EVIDENCE_HEAD_SHA required}"
: "${FA478_EVIDENCE_SOURCE_SHA256:?FA478_EVIDENCE_SOURCE_SHA256 required}"
: "${FA478_FIRST_ERROR_LINE:?FA478_FIRST_ERROR_LINE required}"
: "${FA478_FIRST_ERROR_COL:?FA478_FIRST_ERROR_COL required}"
: "${FA478_FRONTIER_DECLARATION:?FA478_FRONTIER_DECLARATION required}"
: "${FA478_FRONTIER_INDEX:?FA478_FRONTIER_INDEX required}"
: "${FA479_VARIANT:?FA479_VARIANT required}"
: "${FA479_EVIDENCE_RUN_ID:?FA479_EVIDENCE_RUN_ID required}"
: "${FA479_EVIDENCE_JOB_ID:?FA479_EVIDENCE_JOB_ID required}"
: "${FA479_EVIDENCE_HEAD_SHA:?FA479_EVIDENCE_HEAD_SHA required}"
: "${FA479_EVIDENCE_SOURCE_SHA256:?FA479_EVIDENCE_SOURCE_SHA256 required}"
: "${FA479_FIRST_ERROR_LINE:?FA479_FIRST_ERROR_LINE required}"
: "${FA479_FIRST_ERROR_COL:?FA479_FIRST_ERROR_COL required}"
: "${FA479_FRONTIER_DECLARATION:?FA479_FRONTIER_DECLARATION required}"
: "${FA479_FRONTIER_INDEX:?FA479_FRONTIER_INDEX required}"
: "${FA480_VARIANT:?FA480_VARIANT required}"
: "${FA480_EVIDENCE_RUN_ID:?FA480_EVIDENCE_RUN_ID required}"
: "${FA480_EVIDENCE_JOB_ID:?FA480_EVIDENCE_JOB_ID required}"
: "${FA480_EVIDENCE_HEAD_SHA:?FA480_EVIDENCE_HEAD_SHA required}"
: "${FA480_EVIDENCE_SOURCE_SHA256:?FA480_EVIDENCE_SOURCE_SHA256 required}"
: "${FA480_FIRST_ERROR_LINE:?FA480_FIRST_ERROR_LINE required}"
: "${FA480_FIRST_ERROR_COL:?FA480_FIRST_ERROR_COL required}"
: "${FA480_FRONTIER_DECLARATION:?FA480_FRONTIER_DECLARATION required}"
: "${FA480_FRONTIER_INDEX:?FA480_FRONTIER_INDEX required}"
: "${FA481_VARIANT:?FA481_VARIANT required}"
: "${MAX_ERRORS:?MAX_ERRORS required}"

if [[ "$VARIANT" != "norms" || "$MAX_ERRORS" != "32" ]]; then
  echo "FA481 requires VARIANT=norms and MAX_ERRORS=32" >&2
  exit 2
fi
if [[ "$FA480_VARIANT" != "pi_zero_apply" ]]; then
  echo "FA481 requires FA480_VARIANT=pi_zero_apply" >&2
  exit 2
fi
if [[ "$FA480_EVIDENCE_RUN_ID" != "31419752422" || "$FA480_EVIDENCE_JOB_ID" != "93557362741" ]]; then
  echo "FA481 requires exact FA480 run/job evidence" >&2
  exit 2
fi
if [[ "$FA480_EVIDENCE_HEAD_SHA" != "a7b882e84aa31a321e0f108b5f56ca477586ddd8" ]]; then
  echo "FA481 requires exact FA480 evidence head" >&2
  exit 2
fi
if [[ "$FA480_EVIDENCE_SOURCE_SHA256" != "939a4d0db78c0a7e4fadf5a1db97626aaccbb1d7258f6bf77a0ffbede83f52b9" ]]; then
  echo "FA481 requires exact FA480 candidate source hash" >&2
  exit 2
fi
if [[ "$FA480_FIRST_ERROR_LINE" != "35196" || "$FA480_FIRST_ERROR_COL" != "2" ]]; then
  echo "FA481 requires FA480 frontier 35196:2" >&2
  exit 2
fi
if [[ "$FA480_FRONTIER_DECLARATION" != "selectedHeightBasePoint_of_pos" || "$FA480_FRONTIER_INDEX" != "2802" ]]; then
  echo "FA481 requires exact declaration-2802 frontier" >&2
  exit 2
fi
if [[ "$FA481_VARIANT" != "upper_half_plane_ext" ]]; then
  echo "unsupported FA481_VARIANT: $FA481_VARIANT" >&2
  exit 2
fi

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa480_eventually_zero_pi_zero_candidate_ci.sh")
dst = Path("/tmp/fa481_selected_height_upper_ext_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)

text = replace_once(
    text,
    "build-logs/codex-fa480-eventually-zero-pi-zero",
    "build-logs/codex-fa481-selected-height-upper-ext",
)
text = replace_once(
    text,
    "scripts/fa480_prepare_eventually_zero_pi_zero.py",
    "scripts/fa481_prepare_selected_height_upper_ext.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa481_selected_height_upper_ext_candidate_ci.sh
