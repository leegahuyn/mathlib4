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
: "${MAX_ERRORS:?MAX_ERRORS required}"

if [[ "$VARIANT" != "norms" ]]; then
  echo "FA479 requires VARIANT=norms, got: $VARIANT" >&2
  exit 2
fi
if [[ "$MAX_ERRORS" != "32" ]]; then
  echo "FA479 requires MAX_ERRORS=32, got: $MAX_ERRORS" >&2
  exit 2
fi
if [[ "$FA478_VARIANT" != "real_norm_eq_abs_only" ]]; then
  echo "FA479 requires FA478_VARIANT=real_norm_eq_abs_only, got: $FA478_VARIANT" >&2
  exit 2
fi
if [[ "$FA478_EVIDENCE_RUN_ID" != "31416050563" ]]; then
  echo "FA479 requires FA478 evidence run 31416050563, got: $FA478_EVIDENCE_RUN_ID" >&2
  exit 2
fi
if [[ "$FA478_EVIDENCE_JOB_ID" != "93545285888" ]]; then
  echo "FA479 requires FA478 evidence job 93545285888, got: $FA478_EVIDENCE_JOB_ID" >&2
  exit 2
fi
if [[ "$FA478_EVIDENCE_HEAD_SHA" != "46241996e61a001d498ad3e126dc8b38867bff86" ]]; then
  echo "FA479 requires exact FA478 evidence head, got: $FA478_EVIDENCE_HEAD_SHA" >&2
  exit 2
fi
if [[ "$FA478_EVIDENCE_SOURCE_SHA256" != "53a703d3e138ae7a964b7221c52337082cb59820595cfce877a679f024fbcf82" ]]; then
  echo "FA479 requires exact FA478 candidate source hash" >&2
  exit 2
fi
if [[ "$FA478_FIRST_ERROR_LINE" != "35133" || "$FA478_FIRST_ERROR_COL" != "8" ]]; then
  echo "FA479 requires FA478 frontier 35133:8" >&2
  exit 2
fi
if [[ "$FA478_FRONTIER_DECLARATION" != "selectedLogHeightNaturalGauge_eventuallyEq_zero" ]]; then
  echo "FA479 requires exact FA478 frontier declaration" >&2
  exit 2
fi
if [[ "$FA478_FRONTIER_INDEX" != "2796" ]]; then
  echo "FA479 requires exact FA478 frontier declaration index 2796" >&2
  exit 2
fi
if [[ "$FA479_VARIANT" != "simp_only_hlevel" ]]; then
  echo "unsupported FA479_VARIANT: $FA479_VARIANT" >&2
  exit 2
fi

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa477_log_cusp_candidate_ci.sh")
dst = Path("/tmp/fa479_eventually_zero_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)


text = replace_once(
    text,
    "build-logs/codex-fa477-log-cusp",
    "build-logs/codex-fa479-eventually-zero",
)
text = replace_once(
    text,
    "scripts/fa477_prepare_log_cusp.py",
    "scripts/fa479_prepare_eventually_zero.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa479_eventually_zero_candidate_ci.sh
