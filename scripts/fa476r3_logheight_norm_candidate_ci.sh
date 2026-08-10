#!/usr/bin/env bash
set -euo pipefail

: "${HORIZONTAL_STYLE:?HORIZONTAL_STYLE required}"
: "${VARIANT:?VARIANT required}"
: "${FA473_WINNER:?FA473_WINNER required}"
: "${FA474_WINNER:?FA474_WINNER required}"
: "${FA475_WINNER:?FA475_WINNER required}"
: "${FA476_R2_VARIANT:?FA476_R2_VARIANT required}"
: "${FA476_R3_VARIANT:?FA476_R3_VARIANT required}"
: "${MAX_ERRORS:?MAX_ERRORS required}"

if [[ "$VARIANT" != "norms" ]]; then
  echo "FA476-r3 requires VARIANT=norms, got: $VARIANT" >&2
  exit 2
fi
if [[ "$MAX_ERRORS" != "32" ]]; then
  echo "FA476-r3 requires MAX_ERRORS=32, got: $MAX_ERRORS" >&2
  exit 2
fi
if [[ "$FA473_WINNER" != "const_add_simp" ]]; then
  echo "FA476-r3 requires FA473_WINNER=const_add_simp, got: $FA473_WINNER" >&2
  exit 2
fi
if [[ "$FA474_WINNER" != "explicit_through2791" ]]; then
  echo "FA476-r3 requires FA474_WINNER=explicit_through2791, got: $FA474_WINNER" >&2
  exit 2
fi
if [[ "$FA475_WINNER" != "clean_semicolon" ]]; then
  echo "FA476-r3 requires FA475_WINNER=clean_semicolon, got: $FA475_WINNER" >&2
  exit 2
fi
if [[ "$FA476_R2_VARIANT" != "explicit_exp_nonneg" ]]; then
  echo "FA476-r3 requires FA476_R2_VARIANT=explicit_exp_nonneg, got: $FA476_R2_VARIANT" >&2
  exit 2
fi
case "$FA476_R3_VARIANT" in
  minimal_simpa|explicit_dsimp) ;;
  *)
    echo "unsupported FA476_R3_VARIANT: $FA476_R3_VARIANT" >&2
    exit 2
    ;;
esac

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa476_logheight_norm_candidate_ci.sh")
dst = Path("/tmp/fa476r3_logheight_norm_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)


text = replace_once(
    text,
    "build-logs/codex-fa476-logheight-norm",
    "build-logs/codex-fa476r3-logheight-norm",
)
text = replace_once(
    text,
    "scripts/fa476_prepare_logheight_norm.py",
    "scripts/fa476r3_prepare_logheight_norm.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa476r3_logheight_norm_candidate_ci.sh
