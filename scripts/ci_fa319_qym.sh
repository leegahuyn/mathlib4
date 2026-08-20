#!/usr/bin/env bash
set -euo pipefail

# PR #9 keeps this historical entrypoint because the base-branch gate watches
# it. The implementation is strictly the linked PASS 320 candidate, followed
# by PASS 321-r3, PASS 322-r3, FunctionalAnalysis twice, then Integrated/QYM.
exec bash scripts/ci_fa321_qym.sh
