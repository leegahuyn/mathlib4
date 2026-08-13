#!/usr/bin/env bash
# v46 environment adapter for the SHA-locked v42 direct
# Mock2 -> Mock2_Advanced -> Mock2_FunctionalAnalysis(maxErrors=2000) runner.

set -euo pipefail

: "${FA_V46_OUT:?FA_V46_OUT is required}"
: "${FA_V46_EXPECTED_CANDIDATE_SHA256:?FA_V46_EXPECTED_CANDIDATE_SHA256 is required}"
: "${FA_V46_V42_RUNNER_SHA256:?FA_V46_V42_RUNNER_SHA256 is required}"

base_runner="scripts/fa_v42_direct_compile_ci.sh"
[[ -f "$base_runner" ]] || {
  echo "missing locked v42 runner: $base_runner" >&2
  exit 86
}
actual="$(sha256sum "$base_runner" | awk '{print $1}')"
[[ "$actual" == "$FA_V46_V42_RUNNER_SHA256" ]] || {
  echo "v42 runner SHA mismatch" >&2
  exit 86
}

export FA_V42_OUT="$FA_V46_OUT"
export FA_V42_EXPECTED_CANDIDATE_SHA256="$FA_V46_EXPECTED_CANDIDATE_SHA256"
exec bash "$base_runner"
