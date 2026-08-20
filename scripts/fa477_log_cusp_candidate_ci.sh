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
: "${MAX_ERRORS:?MAX_ERRORS required}"

if [[ "$VARIANT" != "norms" ]]; then
  echo "FA477 requires VARIANT=norms, got: $VARIANT" >&2
  exit 2
fi
if [[ "$MAX_ERRORS" != "32" ]]; then
  echo "FA477 requires MAX_ERRORS=32, got: $MAX_ERRORS" >&2
  exit 2
fi
if [[ "$FA473_WINNER" != "const_add_simp" ]]; then
  echo "FA477 requires FA473_WINNER=const_add_simp, got: $FA473_WINNER" >&2
  exit 2
fi
if [[ "$FA474_WINNER" != "explicit_through2791" ]]; then
  echo "FA477 requires FA474_WINNER=explicit_through2791, got: $FA474_WINNER" >&2
  exit 2
fi
if [[ "$FA475_WINNER" != "clean_semicolon" ]]; then
  echo "FA477 requires FA475_WINNER=clean_semicolon, got: $FA475_WINNER" >&2
  exit 2
fi
if [[ "$FA476_R2_VARIANT" != "explicit_exp_nonneg" ]]; then
  echo "FA477 requires FA476_R2_VARIANT=explicit_exp_nonneg, got: $FA476_R2_VARIANT" >&2
  exit 2
fi
if [[ "$FA476_R3_VARIANT" != "minimal_simpa" ]]; then
  echo "FA477 requires FA476_R3_VARIANT=minimal_simpa, got: $FA476_R3_VARIANT" >&2
  exit 2
fi
if [[ "$FA476_R3_EVIDENCE_RUN_ID" != "31407777360" ]]; then
  echo "FA477 requires prior FA476-r3 closure run 31407777360, got: $FA476_R3_EVIDENCE_RUN_ID" >&2
  exit 2
fi
if [[ "$FA476_R3_EVIDENCE_ARTIFACT_ID" != "9070636218" ]]; then
  echo "FA477 requires FA476-r3 evidence artifact 9070636218, got: $FA476_R3_EVIDENCE_ARTIFACT_ID" >&2
  exit 2
fi
if [[ "$FA476_R3_EVIDENCE_ARTIFACT_DIGEST" != "sha256:343607e51bea29fd2878bf6ebfcc0c1c8b1daf9826733b0cd3729e63fbbea3ca" ]]; then
  echo "FA477 requires the exact FA476-r3 evidence artifact digest, got: $FA476_R3_EVIDENCE_ARTIFACT_DIGEST" >&2
  exit 2
fi
case "$FA477_VARIANT" in
  upper_ext_h_simp_only) ;;
  *)
    echo "unsupported FA477_VARIANT: $FA477_VARIANT" >&2
    exit 2
    ;;
esac

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa476r3_logheight_norm_candidate_ci.sh")
dst = Path("/tmp/fa477_log_cusp_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)


text = replace_once(
    text,
    "build-logs/codex-fa476r3-logheight-norm",
    "build-logs/codex-fa477-log-cusp",
)
text = replace_once(
    text,
    "scripts/fa476r3_prepare_logheight_norm.py",
    "scripts/fa477_prepare_log_cusp.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa477_log_cusp_candidate_ci.sh
