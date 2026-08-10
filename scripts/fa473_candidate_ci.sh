#!/usr/bin/env bash
set -euo pipefail

: "${HORIZONTAL_STYLE:?HORIZONTAL_STYLE required}"
: "${VARIANT:?VARIANT required}"
: "${TRACE_VARIANT:?TRACE_VARIANT required}"
: "${MAX_ERRORS:?MAX_ERRORS required}"

if [[ "$VARIANT" != "norms" ]]; then
  echo "FA473 requires VARIANT=norms, got: $VARIANT" >&2
  exit 2
fi
if [[ "$MAX_ERRORS" != "160" ]]; then
  echo "FA473 requires MAX_ERRORS=160, got: $MAX_ERRORS" >&2
  exit 2
fi
case "$TRACE_VARIANT" in
  exp_mul_i|convert_ring_nf|const_add) ;;
  *)
    echo "unsupported TRACE_VARIANT: $TRACE_VARIANT" >&2
    exit 2
    ;;
esac

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa465_candidate_ci.sh")
dst = Path("/tmp/fa473_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)


text = replace_once(
    text,
    "build-logs/fa465-checked-lower",
    "build-logs/codex-fa473-trace-tail",
)
text = replace_once(
    text,
    "scripts/fa465_prepare_checked_lower.py",
    "scripts/fa473_prepare_trace_tail.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa473_candidate_ci.sh
