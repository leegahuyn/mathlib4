#!/usr/bin/env bash
# v65 adapter for the locked v61 -> v59 -> v42 M2 -> M2A -> FA2000 chain.

set -euo pipefail

: "${FA_V65_OUT:?FA_V65_OUT is required}"
: "${FA_V65_EXPECTED_CANDIDATE_SHA256:?candidate SHA is required}"
: "${FA_V65_V61_RUNNER_SHA256:?v61 runner lock is required}"
: "${FA_V65_V59_RUNNER_SHA256:?v59 runner lock is required}"
: "${FA_V65_V42_RUNNER_SHA256:?v42 runner lock is required}"

readonly expected_v61="8a73b654fcf6c79c5141286785016fd4bbb4d35bb0bf697c68210ab5c71fd466"
readonly expected_v59="f744a15a35c3dd38f4a5c5794073616ba626e389db6ca2c4256b12e7624c5ed4"
readonly expected_v42="2459f0a2cd44f6a3716de1ed2934c7588ba1a1e27ef443947d9e6089af196514"

[[ "$FA_V65_V61_RUNNER_SHA256" == "$expected_v61" ]]
[[ "$FA_V65_V59_RUNNER_SHA256" == "$expected_v59" ]]
[[ "$FA_V65_V42_RUNNER_SHA256" == "$expected_v42" ]]
[[ "$(sha256sum scripts/fa_v61_direct_compile_ci.sh | awk '{print $1}')" == "$expected_v61" ]]
[[ "$(sha256sum scripts/fa_v59_direct_compile_ci.sh | awk '{print $1}')" == "$expected_v59" ]]
[[ "$(sha256sum scripts/fa_v42_direct_compile_ci.sh | awk '{print $1}')" == "$expected_v42" ]]

export FA_V61_OUT="$FA_V65_OUT"
export FA_V61_EXPECTED_CANDIDATE_SHA256="$FA_V65_EXPECTED_CANDIDATE_SHA256"
export FA_V61_V59_RUNNER_SHA256="$FA_V65_V59_RUNNER_SHA256"
export FA_V61_V42_RUNNER_SHA256="$FA_V65_V42_RUNNER_SHA256"
exec bash scripts/fa_v61_direct_compile_ci.sh

