#!/usr/bin/env bash
set -euo pipefail

: "${FA482_VARIANT:?FA482_VARIANT required}"
: "${FA482_EVIDENCE_RUN_ID:?FA482_EVIDENCE_RUN_ID required}"
: "${FA482_EVIDENCE_JOB_ID:?FA482_EVIDENCE_JOB_ID required}"
: "${FA482_EVIDENCE_HEAD_SHA:?FA482_EVIDENCE_HEAD_SHA required}"
: "${FA482_EVIDENCE_SOURCE_SHA256:?FA482_EVIDENCE_SOURCE_SHA256 required}"
: "${FA482_FIRST_ERROR_LINE:?FA482_FIRST_ERROR_LINE required}"
: "${FA482_FIRST_ERROR_COL:?FA482_FIRST_ERROR_COL required}"
: "${FA482_FRONTIER_DECLARATION:?FA482_FRONTIER_DECLARATION required}"
: "${FA482_FRONTIER_INDEX:?FA482_FRONTIER_INDEX required}"
: "${FA483_VARIANT:?FA483_VARIANT required}"

if [[ "$FA482_VARIANT" != "remove_complex_mk_im" ]]; then
  echo "FA483 requires FA482_VARIANT=remove_complex_mk_im" >&2
  exit 2
fi
if [[ "$FA482_EVIDENCE_RUN_ID" != "31450425677" ]]; then
  echo "FA483 requires FA482 evidence run 31450425677" >&2
  exit 2
fi
if [[ "$FA482_EVIDENCE_JOB_ID" != "93653492331" ]]; then
  echo "FA483 requires FA482 evidence job 93653492331" >&2
  exit 2
fi
if [[ "$FA482_EVIDENCE_HEAD_SHA" != "a0a19ee27ba6c07d30bdd347150bd71550c80f69" ]]; then
  echo "FA483 requires exact FA482 evidence head" >&2
  exit 2
fi
if [[ "$FA482_EVIDENCE_SOURCE_SHA256" != "daeb276e2c3886ebd9cd93c752e813dc7b288ceb4a872ba734c7634bd0c807ca" ]]; then
  echo "FA483 requires exact FA482 source hash" >&2
  exit 2
fi
if [[ "$FA482_FIRST_ERROR_LINE" != "35203" || "$FA482_FIRST_ERROR_COL" != "2" ]]; then
  echo "FA483 requires FA482 frontier 35203:2" >&2
  exit 2
fi
if [[ "$FA482_FRONTIER_DECLARATION" != "selectedHeightBasePoint_exp" ]]; then
  echo "FA483 requires frontier declaration selectedHeightBasePoint_exp" >&2
  exit 2
fi
if [[ "$FA482_FRONTIER_INDEX" != "2803" ]]; then
  echo "FA483 requires frontier declaration index 2803" >&2
  exit 2
fi
if [[ "$FA483_VARIANT" != "upper_ext_remove_mk_im" ]]; then
  echo "unsupported FA483_VARIANT: $FA483_VARIANT" >&2
  exit 2
fi

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa482_selected_height_remove_mk_im_candidate_ci.sh")
dst = Path("/tmp/fa483_selected_height_exp_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)

text = replace_once(
    text,
    "build-logs/codex-fa482-selected-height-remove-mk-im",
    "build-logs/codex-fa483-selected-height-exp",
)
text = replace_once(
    text,
    "scripts/fa482_prepare_selected_height_remove_mk_im.py",
    "scripts/fa483_prepare_selected_height_exp.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa483_selected_height_exp_candidate_ci.sh
