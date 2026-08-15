#!/usr/bin/env bash
# v63 environment adapter for the exact v61 -> v59 -> v42 M2 -> M2A -> FA2000 chain.

set -euo pipefail

: "${FA_V63_OUT:?FA_V63_OUT is required}"
: "${FA_V63_EXPECTED_CANDIDATE_SHA256:?FA_V63_EXPECTED_CANDIDATE_SHA256 is required}"
: "${FA_V63_V61_RUNNER_SHA256:?FA_V63_V61_RUNNER_SHA256 is required}"
: "${FA_V63_V59_RUNNER_SHA256:?FA_V63_V59_RUNNER_SHA256 is required}"
: "${FA_V63_V42_RUNNER_SHA256:?FA_V63_V42_RUNNER_SHA256 is required}"

v61_runner="scripts/fa_v61_direct_compile_ci.sh"
expected_v61="8a73b654fcf6c79c5141286785016fd4bbb4d35bb0bf697c68210ab5c71fd466"
expected_v59="f744a15a35c3dd38f4a5c5794073616ba626e389db6ca2c4256b12e7624c5ed4"
expected_v42="2459f0a2cd44f6a3716de1ed2934c7588ba1a1e27ef443947d9e6089af196514"

[[ "$FA_V63_V61_RUNNER_SHA256" == "$expected_v61" ]] || {
  echo "v63 configured v61 runner SHA differs from lock" >&2
  exit 86
}
[[ "$FA_V63_V59_RUNNER_SHA256" == "$expected_v59" ]] || {
  echo "v63 configured v59 runner SHA differs from lock" >&2
  exit 86
}
[[ "$FA_V63_V42_RUNNER_SHA256" == "$expected_v42" ]] || {
  echo "v63 configured v42 runner SHA differs from lock" >&2
  exit 86
}
[[ -f "$v61_runner" ]] || {
  echo "missing locked v61 runner: $v61_runner" >&2
  exit 86
}
actual_v61="$(sha256sum "$v61_runner" | awk '{print $1}')"
[[ "$actual_v61" == "$expected_v61" ]] || {
  echo "v61 runner SHA mismatch" >&2
  exit 86
}
[[ "$(wc -c < "$v61_runner" | tr -d '[:space:]')" == "1423" ]] || {
  echo "v61 runner byte mismatch" >&2
  exit 86
}

export FA_V61_OUT="$FA_V63_OUT"
export FA_V61_EXPECTED_CANDIDATE_SHA256="$FA_V63_EXPECTED_CANDIDATE_SHA256"
export FA_V61_V59_RUNNER_SHA256="$FA_V63_V59_RUNNER_SHA256"
export FA_V61_V42_RUNNER_SHA256="$FA_V63_V42_RUNNER_SHA256"
exec bash "$v61_runner"
