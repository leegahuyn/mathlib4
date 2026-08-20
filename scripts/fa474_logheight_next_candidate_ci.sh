#!/usr/bin/env bash
set -euo pipefail

: "${HORIZONTAL_STYLE:?HORIZONTAL_STYLE required}"
: "${VARIANT:?VARIANT required}"
: "${FRONTIER_VARIANT:?FRONTIER_VARIANT required}"
: "${NEXT_VARIANT:?NEXT_VARIANT required}"
: "${MAX_ERRORS:?MAX_ERRORS required}"

if [[ "$VARIANT" != "norms" ]]; then
  echo "FA474 requires VARIANT=norms, got: $VARIANT" >&2
  exit 2
fi
if [[ "$MAX_ERRORS" != "32" ]]; then
  echo "FA474 requires MAX_ERRORS=32, got: $MAX_ERRORS" >&2
  exit 2
fi
case "$FRONTIER_VARIANT" in
  const_add_simp) ;;
  *)
    echo "unsupported FRONTIER_VARIANT: $FRONTIER_VARIANT" >&2
    exit 2
    ;;
esac
case "$NEXT_VARIANT" in
  explicit2790|direct2790|explicit_through2791|direct_through2791) ;;
  *)
    echo "unsupported NEXT_VARIANT: $NEXT_VARIANT" >&2
    exit 2
    ;;
esac

export TRACE_VARIANT="$FRONTIER_VARIANT"

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa473_candidate_ci.sh")
dst = Path("/tmp/fa474_logheight_next_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)


text = replace_once(
    text,
    "build-logs/codex-fa473-trace-tail",
    "build-logs/codex-fa474-logheight-next",
)
text = replace_once(
    text,
    "scripts/fa473_prepare_trace_tail.py",
    "scripts/fa474_prepare_logheight_next.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa474_logheight_next_candidate_ci.sh
