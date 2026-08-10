#!/usr/bin/env bash
set -euo pipefail

TMP="$(mktemp)"
sed \
  -e 's#build-logs/fa457-true-first#build-logs/fa458-cumulative#g' \
  -e 's#fa457_prepare_true_first.py#fa458_prepare_cumulative_continuity.py#g' \
  -e 's#fa457_select_true_first.py#fa458_select_cumulative.py#g' \
  -e 's#fix/fa457-true-error-parser-paired-matrix-20260810#fix/fa458-true-error-cumulative-continuity-20260810#g' \
  -e 's/FA457/FA458/g' \
  scripts/fa457_selector_ci.sh > "$TMP"
chmod +x "$TMP"
exec bash "$TMP"
