#!/usr/bin/env bash
set -euo pipefail
LOGDIR="${FOCUSED_LOGDIR:-/tmp/focused-proof/candidate-v3}"
BUNDLE="${FOCUSED_BUNDLE_OUT:-/tmp/focused-candidate-v3-proof.tar.gz}"
finalize() {
  local code=$?
  mkdir -p "${LOGDIR}"
  printf '%s\n' "${code}" > "${LOGDIR}/pipeline-exit-code.txt"
  tar -czf "${BUNDLE}" -C "$(dirname "${LOGDIR}")" "$(basename "${LOGDIR}")" || true
  return "${code}"
}
trap finalize EXIT
bash scripts/focused_materialize_pipeline_20260807.sh
