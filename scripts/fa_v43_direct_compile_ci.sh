#!/usr/bin/env bash
# v43 environment adapter for the already-promoted, SHA-locked v42 direct
# M2 -> M2A -> FA highcap2000 runner.

set -euo pipefail

: "${FA_V43_OUT:?FA_V43_OUT is required}"
: "${FA_V43_EXPECTED_CANDIDATE_SHA256:?FA_V43_EXPECTED_CANDIDATE_SHA256 is required}"
: "${FA_V43_V42_RUNNER_SHA256:?FA_V43_V42_RUNNER_SHA256 is required}"

base_runner="scripts/fa_v42_direct_compile_ci.sh"
[[ -f "$base_runner" ]] || {
  echo "missing locked v42 runner: $base_runner" >&2
  exit 86
}
actual="$(sha256sum "$base_runner" | awk '{print $1}')"
[[ "$actual" == "$FA_V43_V42_RUNNER_SHA256" ]] || {
  echo "v42 runner SHA mismatch" >&2
  exit 86
}

export FA_V42_OUT="$FA_V43_OUT"
export FA_V42_EXPECTED_CANDIDATE_SHA256="$FA_V43_EXPECTED_CANDIDATE_SHA256"
exec bash "$base_runner"
