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
: "${MAX_ERRORS:?MAX_ERRORS required}"

if [[ "$VARIANT" != "norms" ]]; then
  echo "FA478 requires VARIANT=norms, got: $VARIANT" >&2
  exit 2
fi
if [[ "$MAX_ERRORS" != "32" ]]; then
  echo "FA478 requires MAX_ERRORS=32, got: $MAX_ERRORS" >&2
  exit 2
fi
if [[ "$FA473_WINNER" != "const_add_simp" ]]; then
  echo "FA478 requires FA473_WINNER=const_add_simp, got: $FA473_WINNER" >&2
  exit 2
fi
if [[ "$FA474_WINNER" != "explicit_through2791" ]]; then
  echo "FA478 requires FA474_WINNER=explicit_through2791, got: $FA474_WINNER" >&2
  exit 2
fi
if [[ "$FA475_WINNER" != "clean_semicolon" ]]; then
  echo "FA478 requires FA475_WINNER=clean_semicolon, got: $FA475_WINNER" >&2
  exit 2
fi
if [[ "$FA476_R2_VARIANT" != "explicit_exp_nonneg" ]]; then
  echo "FA478 requires FA476_R2_VARIANT=explicit_exp_nonneg, got: $FA476_R2_VARIANT" >&2
  exit 2
fi
if [[ "$FA476_R3_VARIANT" != "minimal_simpa" ]]; then
  echo "FA478 requires FA476_R3_VARIANT=minimal_simpa, got: $FA476_R3_VARIANT" >&2
  exit 2
fi
if [[ "$FA476_R3_EVIDENCE_RUN_ID" != "31407777360" ]]; then
  echo "FA478 requires FA476-r3 evidence run 31407777360, got: $FA476_R3_EVIDENCE_RUN_ID" >&2
  exit 2
fi
if [[ "$FA476_R3_EVIDENCE_ARTIFACT_ID" != "9070636218" ]]; then
  echo "FA478 requires FA476-r3 evidence artifact 9070636218, got: $FA476_R3_EVIDENCE_ARTIFACT_ID" >&2
  exit 2
fi
if [[ "$FA476_R3_EVIDENCE_ARTIFACT_DIGEST" != "sha256:343607e51bea29fd2878bf6ebfcc0c1c8b1daf9826733b0cd3729e63fbbea3ca" ]]; then
  echo "FA478 requires the exact FA476-r3 evidence artifact digest" >&2
  exit 2
fi
if [[ "$FA477_VARIANT" != "upper_ext_h_simp_only" ]]; then
  echo "FA478 requires FA477_VARIANT=upper_ext_h_simp_only, got: $FA477_VARIANT" >&2
  exit 2
fi
if [[ "$FA477_EVIDENCE_RUN_ID" != "31409787172" ]]; then
  echo "FA478 requires authoritative FA477 closure run 31409787172, got: $FA477_EVIDENCE_RUN_ID" >&2
  exit 2
fi
if [[ "$FA477_EVIDENCE_JOB_ID" != "93524786715" ]]; then
  echo "FA478 requires FA477 evidence job 93524786715, got: $FA477_EVIDENCE_JOB_ID" >&2
  exit 2
fi
if [[ "$FA477_EVIDENCE_HEAD_SHA" != "faf902ceda7cce10ada4399326330effaa4d669b" ]]; then
  echo "FA478 requires the exact FA477 evidence head, got: $FA477_EVIDENCE_HEAD_SHA" >&2
  exit 2
fi
if [[ "$FA477_EVIDENCE_ARTIFACT_ID" != "9071387258" ]]; then
  echo "FA478 requires FA477 evidence artifact 9071387258, got: $FA477_EVIDENCE_ARTIFACT_ID" >&2
  exit 2
fi
if [[ "$FA477_EVIDENCE_ARTIFACT_NAME" != "codex-fa477-minimal_simpa-run31407777360-artifact9070636218-upper_ext_h_simp_only" ]]; then
  echo "FA478 requires the exact FA477 evidence artifact name" >&2
  exit 2
fi
if [[ "$FA477_EVIDENCE_ARTIFACT_SIZE" != "598253" ]]; then
  echo "FA478 requires FA477 evidence artifact size 598253, got: $FA477_EVIDENCE_ARTIFACT_SIZE" >&2
  exit 2
fi
if [[ "$FA477_EVIDENCE_ARTIFACT_DIGEST" != "sha256:25928120f3113f98886a469b255eec59754bfd232b4df621f4efa4e1e9940b81" ]]; then
  echo "FA478 requires the exact FA477 evidence artifact digest" >&2
  exit 2
fi
if [[ "$FA478_VARIANT" != "real_norm_eq_abs_only" ]]; then
  echo "unsupported FA478_VARIANT: $FA478_VARIANT" >&2
  exit 2
fi

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa477_log_cusp_candidate_ci.sh")
dst = Path("/tmp/fa478_normsq_log_cusp_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)


text = replace_once(
    text,
    "build-logs/codex-fa477-log-cusp",
    "build-logs/codex-fa478-normsq-log-cusp",
)
text = replace_once(
    text,
    "scripts/fa477_prepare_log_cusp.py",
    "scripts/fa478_prepare_normsq_log_cusp.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa478_normsq_log_cusp_candidate_ci.sh
