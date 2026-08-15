#!/usr/bin/env bash
# v61 environment adapter for the SHA-locked v59 -> v42 M2 -> M2A -> FA chain.

set -euo pipefail

: "${FA_V61_OUT:?FA_V61_OUT is required}"
: "${FA_V61_EXPECTED_CANDIDATE_SHA256:?FA_V61_EXPECTED_CANDIDATE_SHA256 is required}"
: "${FA_V61_V59_RUNNER_SHA256:?FA_V61_V59_RUNNER_SHA256 is required}"
: "${FA_V61_V42_RUNNER_SHA256:?FA_V61_V42_RUNNER_SHA256 is required}"

v59_runner="scripts/fa_v59_direct_compile_ci.sh"
expected_v59="f744a15a35c3dd38f4a5c5794073616ba626e389db6ca2c4256b12e7624c5ed4"
[[ "$FA_V61_V59_RUNNER_SHA256" == "$expected_v59" ]] || {
  echo "v61 configured v59 runner SHA differs from the lock" >&2
  exit 86
}
[[ -f "$v59_runner" ]] || {
  echo "missing locked v59 runner: $v59_runner" >&2
  exit 86
}
actual_v59="$(sha256sum "$v59_runner" | awk '{print $1}')"
[[ "$actual_v59" == "$expected_v59" ]] || {
  echo "v59 runner SHA mismatch" >&2
  exit 86
}
[[ "$(wc -c < "$v59_runner" | tr -d '[:space:]')" == "1073" ]] || {
  echo "v59 runner byte mismatch" >&2
  exit 86
}

expected_v42="2459f0a2cd44f6a3716de1ed2934c7588ba1a1e27ef443947d9e6089af196514"
[[ "$FA_V61_V42_RUNNER_SHA256" == "$expected_v42" ]] || {
  echo "v61 configured v42 runner SHA differs from the lock" >&2
  exit 86
}

export FA_V59_OUT="$FA_V61_OUT"
export FA_V59_EXPECTED_CANDIDATE_SHA256="$FA_V61_EXPECTED_CANDIDATE_SHA256"
export FA_V59_V42_RUNNER_SHA256="$FA_V61_V42_RUNNER_SHA256"
exec bash "$v59_runner"
