#!/usr/bin/env bash
set -euo pipefail

require_eq() {
  local name="$1"
  local expected="$2"
  local actual="${!name-}"
  if [[ "$actual" != "$expected" ]]; then
    printf 'FA506 evidence gate: %s must equal %q, got %q\n' "$name" "$expected" "$actual" >&2
    exit 86
  fi
}

require_positive_decimal() {
  local name="$1"
  local actual="${!name-}"
  if [[ ! "$actual" =~ ^[1-9][0-9]*$ ]]; then
    printf 'FA506 evidence gate: %s must be a verified positive decimal, got %q\n' "$name" "$actual" >&2
    exit 86
  fi
}

require_sha40() {
  local name="$1"
  local actual="${!name-}"
  if [[ ! "$actual" =~ ^[0-9a-f]{40}$ || "$actual" == 0000000000000000000000000000000000000000 ]]; then
    printf 'FA506 evidence gate: %s must be a verified nonzero 40-hex SHA, got %q\n' "$name" "$actual" >&2
    exit 86
  fi
}

require_eq FA505_EVIDENCE_STATUS VERIFIED
require_positive_decimal FA505_EVIDENCE_RUN_ID
require_positive_decimal FA505_EVIDENCE_JOB_ID
require_sha40 FA505_EVIDENCE_HEAD_SHA
require_eq FA505_EVIDENCE_SOURCE_SHA256 c56e320e31dbb4c2d80a7b6c05e3417b9683fe982a9f006bbd6166add95ea9e7
require_eq FA505_CLASSIFICATION LEAN_FAILURE
require_eq FA505_INFRA_REASONS '[]'
require_eq FA505_MOCK2_EXIT 0
require_eq FA505_MOCK2_ADVANCED_EXIT 0
require_eq FA505_FA_EXIT 1
require_eq FA505_PREVIOUS_FRONTIER_DECLARATION integral_selectedHeightGraphDensity_stripTail_eq_iterated
require_eq FA505_PREVIOUS_FRONTIER_INDEX 2835
require_eq FA505_FIRST_ERROR_DECLARATION complex_image_heightStrip_eq_coe_image_selectedBaseCuspStrip
require_eq FA505_FIRST_ERROR_INDEX 2839
require_positive_decimal FA505_FIRST_ERROR_LINE
require_positive_decimal FA505_FIRST_ERROR_COL

export FA506_VARIANT=explicit_upper_half_plane_coe_projections
export FA_COMPILE_MAX_ERRORS="${FA_COMPILE_MAX_ERRORS:-32}"

python3 - <<'PY'
from pathlib import Path

src = Path('scripts/fa505_height_graph_strip_fubini_candidate_ci.sh')
dst = Path('/tmp/fa506_complex_height_strip_coe_candidate_ci.sh')
text = src.read_text(encoding='utf-8')


def once(old: str, new: str) -> None:
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'expected one {old!r}, got {count}')
    text = text.replace(old, new, 1)


once(
    'build-logs/codex-fa505-height-graph-strip-fubini',
    'build-logs/codex-fa506-complex-height-strip-coe',
)
once(
    'scripts/fa505_prepare_height_graph_strip_fubini.py',
    'scripts/fa506_prepare_complex_height_strip_coe.py',
)
dst.write_text(text, encoding='utf-8')
PY

exec bash /tmp/fa506_complex_height_strip_coe_candidate_ci.sh
