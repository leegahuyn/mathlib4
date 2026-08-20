#!/usr/bin/env bash
# v59 environment adapter for the SHA-locked v42 direct M2 -> M2A -> FA runner.

set -euo pipefail

: "${FA_V59_OUT:?FA_V59_OUT is required}"
: "${FA_V59_EXPECTED_CANDIDATE_SHA256:?FA_V59_EXPECTED_CANDIDATE_SHA256 is required}"
: "${FA_V59_V42_RUNNER_SHA256:?FA_V59_V42_RUNNER_SHA256 is required}"

base_runner="scripts/fa_v42_direct_compile_ci.sh"
expected="2459f0a2cd44f6a3716de1ed2934c7588ba1a1e27ef443947d9e6089af196514"
[[ "$FA_V59_V42_RUNNER_SHA256" == "$expected" ]] || {
  echo "v59 configured v42 runner SHA differs from the promoted lock" >&2
  exit 86
}
[[ -f "$base_runner" ]] || {
  echo "missing locked v42 runner: $base_runner" >&2
  exit 86
}
actual="$(sha256sum "$base_runner" | awk '{print $1}')"
[[ "$actual" == "$expected" ]] || {
  echo "v42 runner SHA mismatch" >&2
  exit 86
}
[[ "$(wc -c < "$base_runner" | tr -d '[:space:]')" == "2554" ]] || {
  echo "v42 runner byte mismatch" >&2
  exit 86
}

export FA_V42_OUT="$FA_V59_OUT"
export FA_V42_EXPECTED_CANDIDATE_SHA256="$FA_V59_EXPECTED_CANDIDATE_SHA256"
exec bash "$base_runner"
