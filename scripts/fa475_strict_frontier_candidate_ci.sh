#!/usr/bin/env bash
set -euo pipefail

: "${HORIZONTAL_STYLE:?HORIZONTAL_STYLE required}"
: "${VARIANT:?VARIANT required}"
: "${FA473_WINNER:?FA473_WINNER required}"
: "${FA474_WINNER:?FA474_WINNER required}"
: "${FA475_VARIANT:?FA475_VARIANT required}"
: "${MAX_ERRORS:?MAX_ERRORS required}"

if [[ "$VARIANT" != "norms" ]]; then
  echo "FA475 requires VARIANT=norms, got: $VARIANT" >&2
  exit 2
fi
if [[ "$MAX_ERRORS" != "32" ]]; then
  echo "FA475 requires MAX_ERRORS=32, got: $MAX_ERRORS" >&2
  exit 2
fi
if [[ "$FA473_WINNER" != "const_add_simp" ]]; then
  echo "FA475 requires FA473_WINNER=const_add_simp, got: $FA473_WINNER" >&2
  exit 2
fi
if [[ "$FA474_WINNER" != "explicit_through2791" ]]; then
  echo "FA475 requires FA474_WINNER=explicit_through2791, got: $FA474_WINNER" >&2
  exit 2
fi
case "$FA475_VARIANT" in
  simp_h_ring|simp_h_comm_ring|simp_h_ring_nf|norm_cast_h_ring_nf|norm_num_h_ring_nf) ;;
  *)
    echo "unsupported FA475_VARIANT: $FA475_VARIANT" >&2
    exit 2
    ;;
esac

export FRONTIER_VARIANT="$FA473_WINNER"
export NEXT_VARIANT="$FA474_WINNER"

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa474_logheight_next_candidate_ci.sh")
dst = Path("/tmp/fa475_strict_frontier_candidate_ci.sh")
text = src.read_text(encoding="utf-8")


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence of {old!r}, found {count}")
    return text.replace(old, new, 1)


text = replace_once(
    text,
    "build-logs/codex-fa474-logheight-next",
    "build-logs/codex-fa475-strict-frontier",
)
text = replace_once(
    text,
    "scripts/fa474_prepare_logheight_next.py",
    "scripts/fa475_prepare_strict_frontier.py",
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa475_strict_frontier_candidate_ci.sh
