#!/usr/bin/env bash
# Direct Lean compile runner for the fail-closed FA v41 GitHub package.
#
# This script is intended to run only after the workflow has materialized and
# SHA-locked the cumulative candidate.  It deliberately captures Lean exit
# statuses instead of returning early, so the always() evidence steps can
# upload every raw log.  The workflow's final gate owns the authoritative exit.

set -euo pipefail

OUT="${FA_V41_OUT:?FA_V41_OUT is required}"
EXPECTED="${FA_V41_EXPECTED_CANDIDATE_SHA256:?FA_V41_EXPECTED_CANDIDATE_SHA256 is required}"
SOURCE="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
OLEAN_ROOT=".lake/build/lib/lean/PrimalitySheafVerification"

if [[ ! "$EXPECTED" =~ ^[0-9a-f]{64}$ ]] || [[ "$EXPECTED" =~ ^0{64}$ ]]; then
  printf '%s\n' "invalid or pending FA_V41_EXPECTED_CANDIDATE_SHA256" >&2
  exit 86
fi

mkdir -p "$OUT" "$OLEAN_ROOT"
test -f "$SOURCE" || exit 86

actual_before="$(sha256sum "$SOURCE" | awk '{print $1}')"
printf '%s\n' "$actual_before" >"$OUT/candidate.before.sha256"
test "$actual_before" = "$EXPECTED" || exit 86

one() {
  local stem="$1"
  local cap="$2"
  local source_path="PrimalitySheafVerification/${stem}.lean"
  local olean="${OLEAN_ROOT}/${stem}.olean"
  local ilean="${OLEAN_ROOT}/${stem}.ilean"

  test -f "$source_path" || return 86
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
test "$actual_before_fa" = "$EXPECTED" || exit 86

one Mock2_FunctionalAnalysis 2000

actual_after="$(sha256sum "$SOURCE" | awk '{print $1}')"
printf '%s\n' "$actual_after" >"$OUT/candidate.after.sha256"
test "$actual_after" = "$EXPECTED" || exit 86

