#!/usr/bin/env bash
# Direct M2 -> M2A -> FA compiler runner for an exact FA v42 candidate.
# Exit statuses are captured rather than propagated so always() evidence and
# the final mirror gate remain authoritative.

set -euo pipefail

OUT="${FA_V42_OUT:?FA_V42_OUT is required}"
EXPECTED="${FA_V42_EXPECTED_CANDIDATE_SHA256:?FA_V42_EXPECTED_CANDIDATE_SHA256 is required}"
SOURCE="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
OLEAN_ROOT=".lake/build/lib/lean/PrimalitySheafVerification"
STEMS=(Mock2 Mock2_Advanced Mock2_FunctionalAnalysis)

mkdir -p "$OUT" "$OLEAN_ROOT"

fail_all() {
  local reason="$1"
  for stem in "${STEMS[@]}"; do
    : >"$OUT/${stem}.log"
    printf '%s\n' "$reason" >"$OUT/${stem}.log"
    printf '%s\n' 86 >"$OUT/${stem}.exit"
    : >"$OUT/${stem}.command"
  done
  exit 86
}

if [[ ! "$EXPECTED" =~ ^[0-9a-f]{64}$ ]] || [[ "$EXPECTED" =~ ^0{64}$ ]]; then
  fail_all "invalid or pending FA_V42_EXPECTED_CANDIDATE_SHA256"
fi
[[ -f "$SOURCE" ]] || fail_all "missing exact FA candidate source"

actual_before="$(sha256sum "$SOURCE" | awk '{print $1}')"
printf '%s\n' "$actual_before" >"$OUT/candidate.before.sha256"
[[ "$actual_before" == "$EXPECTED" ]] || fail_all "candidate SHA mismatch before direct chain"

one() {
  local stem="$1"
  local cap="$2"
  local source_path="PrimalitySheafVerification/${stem}.lean"
  local olean="${OLEAN_ROOT}/${stem}.olean"
  local ilean="${OLEAN_ROOT}/${stem}.ilean"

  if [[ ! -f "$source_path" ]]; then
    printf '%s\n' "missing source: $source_path" >"$OUT/${stem}.log"
    printf '%s\n' 86 >"$OUT/${stem}.exit"
    : >"$OUT/${stem}.command"
    return 0
  fi
  rm -f -- "$olean" "$ilean"
  : >"$OUT/${stem}.executed"
  printf '%q ' lake env lean "-DmaxErrors=${cap}" -DwarningAsError=false \
    -o "$olean" -i "$ilean" "$source_path" >"$OUT/${stem}.command"
  printf '\n' >>"$OUT/${stem}.command"

  set +e
  lake env lean "-DmaxErrors=${cap}" -DwarningAsError=false \
    -o "$olean" -i "$ilean" "$source_path" \
    >"$OUT/${stem}.log" 2>&1
  local status=$?
  set -e
  printf '%s\n' "$status" >"$OUT/${stem}.exit"
}

one Mock2 1
one Mock2_Advanced 1

actual_before_fa="$(sha256sum "$SOURCE" | awk '{print $1}')"
printf '%s\n' "$actual_before_fa" >"$OUT/candidate.before-fa.sha256"
[[ "$actual_before_fa" == "$EXPECTED" ]] || fail_all "candidate SHA mismatch before FA"

one Mock2_FunctionalAnalysis 2000

actual_after="$(sha256sum "$SOURCE" | awk '{print $1}')"
printf '%s\n' "$actual_after" >"$OUT/candidate.after.sha256"
[[ "$actual_after" == "$EXPECTED" ]] || exit 86
