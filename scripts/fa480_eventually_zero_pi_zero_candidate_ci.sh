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
: "${MAX_ERRORS:?MAX_ERRORS required}"

if [[ "$VARIANT" != "norms" ]]; then
  echo "FA480 requires VARIANT=norms, got: $VARIANT" >&2
  exit 2
fi
if [[ "$MAX_ERRORS" != "32" ]]; then
  echo "FA480 requires MAX_ERRORS=32, got: $MAX_ERRORS" >&2
  exit 2
fi
if [[ "$FA479_VARIANT" != "simp_only_hlevel" ]]; then
  echo "FA480 requires FA479_VARIANT=simp_only_hlevel, got: $FA479_VARIANT" >&2
  exit 2
fi
if [[ "$FA479_EVIDENCE_RUN_ID" != "31418190945" ]]; then
  echo "FA480 requires FA479 evidence run 31418190945, got: $FA479_EVIDENCE_RUN_ID" >&2
  exit 2
fi
if [[ "$FA479_EVIDENCE_JOB_ID" != "93552181972" ]]; then
  echo "FA480 requires FA479 evidence job 93552181972, got: $FA479_EVIDENCE_JOB_ID" >&2
  exit 2
fi
if [[ "$FA479_EVIDENCE_HEAD_SHA" != "23432f72b76df7a708322ad12afa4ac807fce722" ]]; then
  echo "FA480 requires exact FA479 evidence head, got: $FA479_EVIDENCE_HEAD_SHA" >&2
  exit 2
fi
if [[ "$FA479_EVIDENCE_SOURCE_SHA256" != "9e88d79d650d9a9a2f334aceb14f0ef14890f62785f045e03ffb073fd007eb3a" ]]; then
  echo "FA480 requires exact FA479 candidate source hash" >&2
  exit 2
fi
if [[ "$FA479_FIRST_ERROR_LINE" != "35118" || "$FA479_FIRST_ERROR_COL" != "64" ]]; then
  echo "FA480 requires FA479 frontier 35118:64" >&2
  exit 2
fi
if [[ "$FA479_FRONTIER_DECLARATION" != "selectedLogHeightNaturalGauge_eventuallyEq_zero" ]]; then
  echo "FA480 requires exact FA479 frontier declaration" >&2
  exit 2
fi
if [[ "$FA479_FRONTIER_INDEX" != "2796" ]]; then
  echo "FA480 requires exact FA479 frontier declaration index 2796" >&2
  exit 2
fi
if [[ "$FA480_VARIANT" != "pi_zero_apply" ]]; then
  echo "unsupported FA480_VARIANT: $FA480_VARIANT" >&2
  exit 2
fi

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa479_eventually_zero_candidate_ci.sh")
dst = Path("/tmp/fa480_eventually_zero_pi_zero_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)

text = replace_once(
    text,
    "build-logs/codex-fa479-eventually-zero",
    "build-logs/codex-fa480-eventually-zero-pi-zero",
)
text = replace_once(
    text,
    "scripts/fa479_prepare_eventually_zero.py",
    "scripts/fa480_prepare_eventually_zero_pi_zero.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa480_eventually_zero_pi_zero_candidate_ci.sh
