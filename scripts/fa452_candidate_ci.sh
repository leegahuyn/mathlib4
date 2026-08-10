#!/usr/bin/env bash
set +e
: "${VARIANT:?VARIANT required}"

OUT="build-logs/fa452-compact-energy/candidates/${VARIANT}"
MAX_ERRORS="${MAX_ERRORS:-160}"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
rm -rf "$OUT"
mkdir -p "$OUT" .lake/build/lib/lean/PrimalitySheafVerification

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git rev-parse HEAD > "$OUT/repository-head.txt"

python3 scripts/fa452_prepare_compact_energy_v2.py \
  --variant "$VARIANT" --output-dir "$OUT" > "$OUT/prepare.log" 2>&1
prepare_rc=$?
printf '%s' "$prepare_rc" > "$OUT/prepare.exit"
cat "$OUT/prepare.log"

curl --retry 5 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -o /tmp/elan-init.sh > "$OUT/elan-download.log" 2>&1
curl_rc=$?
printf '%s' "$curl_rc" > "$OUT/elan-download.exit"
install_rc=125
if test "$curl_rc" -eq 0; then
  sh /tmp/elan-init.sh -y --default-toolchain none > "$OUT/elan-init.log" 2>&1
  elan_rc=$?
  if test "$elan_rc" -eq 0; then
    export PATH="${HOME}/.elan/bin:${PATH}"
    elan toolchain install "$(cat lean-toolchain)" > "$OUT/toolchain-install.log" 2>&1
    install_rc=$?
  fi
fi
printf '%s' "$install_rc" > "$OUT/toolchain-install.exit"
export PATH="${HOME}/.elan/bin:${PATH}"

cache_rc=125
if test "$install_rc" -eq 0; then
  lean --version > "$OUT/lean-version.txt" 2>&1
  lake --version > "$OUT/lake-version.txt" 2>&1
  lake exe cache get > "$OUT/cache-get.log" 2>&1
  cache_rc=$?
fi
printf '%s' "$cache_rc" > "$OUT/cache-get.exit"

compile_one() {
  local stem="$1"
  local cap="$2"
  local src="PrimalitySheafVerification/${stem}.lean"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  rm -f "$o" "$i"
  local command=(lake env lean "-DmaxErrors=${cap}" -DwarningAsError=false \
    -o "$o" -i "$i" "$src")
  printf '%q ' "${command[@]}" > "$OUT/${stem}.command"
  printf '\n' >> "$OUT/${stem}.command"
  touch "$OUT/${stem}.executed"
  "${command[@]}" > "$OUT/${stem}.log" 2>&1
  local rc=$?
  printf '%s' "$rc" > "$OUT/${stem}.exit"
  if test "$rc" -eq 0 && test -s "$o" && test -s "$i"; then
    printf true > "$OUT/${stem}.artifacts_ok"
  else
    printf false > "$OUT/${stem}.artifacts_ok"
  fi
}

if test "$prepare_rc" -eq 0 && test "$install_rc" -eq 0 && test "$cache_rc" -eq 0; then
  compile_one Mock2 60
  compile_one Mock2_Advanced 60
  compile_one Mock2_FunctionalAnalysis "$MAX_ERRORS"
else
  for stem in Mock2 Mock2_Advanced Mock2_FunctionalAnalysis; do
    printf '125' > "$OUT/${stem}.exit"
    printf 'not executed: prepare=%s install=%s cache=%s\n' \
      "$prepare_rc" "$install_rc" "$cache_rc" > "$OUT/${stem}.log"
    printf 'INFRA_FAILURE: command not executed\n' > "$OUT/${stem}.command"
    printf false > "$OUT/${stem}.artifacts_ok"
  done
fi

export VARIANT
export FA442_OUT_DIR="$OUT"
export FA442_SOURCE="$SRC"
export FA442_METADATA="$OUT/CANDIDATE.json"
export FA442_EXPECTED_LINES="$(python3 - <<'PY'
from pathlib import Path
p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
d=p.read_bytes()
print(d.count(b'\n') + (0 if d.endswith(b'\n') else 1))
PY
)"
export MAX_ERRORS
python3 scripts/fa442_record_direct_metric.py > "$OUT/metric-console.log" 2>&1
metric_rc=$?
printf '%s' "$metric_rc" > "$OUT/metric.exit"
cat "$OUT/metric-console.log"
exit 0
