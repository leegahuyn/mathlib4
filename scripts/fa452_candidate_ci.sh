#!/usr/bin/env bash
set -euo pipefail

VARIANT="${VARIANT:?VARIANT is required}"
MAX_ERRORS="${MAX_ERRORS:-160}"
BASE="build-logs/fa452-compact-support/candidates/${VARIANT}"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
mkdir -p "$BASE" .lake/build/lib/lean/PrimalitySheafVerification

# Candidate generation is permitted to fail, but never suppresses infrastructure evidence.
set +e
python3 scripts/fa452_prepare_compact_support.py \
  --variant "$VARIANT" --output-dir "$BASE" \
  > "$BASE/prepare.log" 2>&1
prepare_rc=$?
set -e
cat "$BASE/prepare.log"
printf '%s' "$prepare_rc" > "$BASE/prepare.exit"

curl --retry 5 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none > "$BASE/elan-init.log" 2>&1
export PATH="${HOME}/.elan/bin:${PATH}"
elan toolchain install "$(cat lean-toolchain)" > "$BASE/toolchain-install.log" 2>&1
printf '0' > "$BASE/toolchain-install.exit"
lean --version | tee "$BASE/lean-version.txt"
lake --version | tee "$BASE/lake-version.txt"
lake exe cache get | tee "$BASE/cache-get.log"
printf '0' > "$BASE/cache-get.exit"

compile_one() {
  local stem="$1" cap="$2"
  local source="PrimalitySheafVerification/${stem}.lean"
  local olean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local ilean=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  local command=(
    lake env lean "-DmaxErrors=${cap}" -DwarningAsError=false
    -o "$olean" -i "$ilean" "$source"
  )
  rm -f "$olean" "$ilean"
  printf '%q ' "${command[@]}" > "$BASE/${stem}.command"
  printf '\n' >> "$BASE/${stem}.command"
  if test "$prepare_rc" -ne 0; then
    printf '125' > "$BASE/${stem}.exit"
    printf 'false' > "$BASE/${stem}.artifacts_ok"
    printf 'INFRA_FAILURE: candidate preparation failed before direct Lean CLI\n' \
      > "$BASE/${stem}.log"
    return 0
  fi
  touch "$BASE/${stem}.executed"
  set +e
  "${command[@]}" > "$BASE/${stem}.log" 2>&1
  local rc=$?
  set -e
  printf '%s' "$rc" > "$BASE/${stem}.exit"
  if test "$rc" -eq 0 && test -s "$olean" && test -s "$ilean"; then
    printf 'true' > "$BASE/${stem}.artifacts_ok"
  else
    printf 'false' > "$BASE/${stem}.artifacts_ok"
  fi
}

compile_one Mock2 50
compile_one Mock2_Advanced 50
compile_one Mock2_FunctionalAnalysis "$MAX_ERRORS"

export FA442_OUT_DIR="$BASE"
export FA442_SOURCE="$SRC"
export FA442_METADATA="$BASE/CANDIDATE.json"
export FA442_EXPECTED_LINES="$(python3 - <<'PY'
from pathlib import Path
p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
if not p.exists():
    print(0)
else:
    data=p.read_bytes()
    print(data.count(b'\n') + (0 if data.endswith(b'\n') else 1))
PY
)"
export MAX_ERRORS
set +e
python3 scripts/fa442_record_direct_metric.py > "$BASE/metric-console.log" 2>&1
metric_rc=$?
set -e
cat "$BASE/metric-console.log"
printf '%s' "$metric_rc" > "$BASE/metric.exit"

# Metric generation itself is an infrastructure requirement.
test -s "$BASE/METRIC.json"
