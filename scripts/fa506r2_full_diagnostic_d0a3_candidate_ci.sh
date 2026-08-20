#!/usr/bin/env bash
set -euo pipefail

die() {
  printf 'FA506-r2 full diagnostic gate: %s\n' "$*" >&2
  exit 86
}

require_file_sha() {
  local path="$1" expected="$2"
  [[ -f "$path" ]] || die "missing locked dependency $path"
  local actual
  actual="$(sha256sum "$path" | awk '{print $1}')"
  [[ "$actual" == "$expected" ]] ||
    die "$path SHA drift: $actual; expected $expected"
}

[[ "${FA506R2_VARIANT-}" == membership_plus_frontier_batch ]] ||
  die "FA506R2_VARIANT must be membership_plus_frontier_batch"
[[ "${FA506R2_EXPECTED_SHA256-}" == \
  d0a3decee1c0a7a781d14fdf122e235d71d8f210bb65a894dc4e518821bf03ec ]] ||
  die "candidate SHA environment drift"
[[ "${FA506R2_EXPECTED_BYTES-}" == 2702252 ]] ||
  die "candidate byte environment drift"
[[ "${FA506R2_EXPECTED_LINES-}" == 60573 ]] ||
  die "candidate line environment drift"
[[ "${FA_COMPILE_MAX_ERRORS-}" == 2000 ]] ||
  die "FA_COMPILE_MAX_ERRORS must be exactly 2000"

require_file_sha scripts/fa507_prepare_frontier_2840_2888_cumulative.py \
  d824501a7428c72b64153d1ccb090edf5b6ff413c582c13644121f4308d4234e
require_file_sha scripts/fa506r2_prepare_forward_mem_prod_matrix.py \
  b080cd6c067961dcd497cdbbe8827976084cff63d401fcd038ecfa2aa3ca5cf6
require_file_sha scripts/fa506r2_forward_mem_prod_matrix_candidate_ci.sh \
  01743c04417942ae1eec3e9479b9b4b94156b6515b4a805506aa14733bca6e6e

python3 - <<'PY'
from pathlib import Path

src = Path("scripts/fa506r2_forward_mem_prod_matrix_candidate_ci.sh")
dst = Path("/tmp/fa506r2-full-diagnostic-d0a3-candidate-ci.sh")
text = src.read_text(encoding="utf-8")


def once(old: str, new: str) -> None:
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one {old!r}, got {count}")
    text = text.replace(old, new, 1)


once(
    "require_eq FA_COMPILE_MAX_ERRORS 32",
    "require_eq FA_COMPILE_MAX_ERRORS 2000",
)
once(
    'f"build-logs/codex-fa506r2-forward-mem-prod-{variant}"',
    '"build-logs/codex-fa506r2-full-diagnostic-d0a3"',
)
dst.write_text(text, encoding="utf-8")
PY

exec bash /tmp/fa506r2-full-diagnostic-d0a3-candidate-ci.sh
