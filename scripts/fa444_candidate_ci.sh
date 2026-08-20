#!/usr/bin/env bash
set +e

: "${VARIANT:?VARIANT is required}"
MAX_ERRORS="${MAX_ERRORS:-50}"
ROOT="$(pwd)"
OUT="${FA444_OUT_DIR:-build-logs/fa442-pipeline-repair/candidates/${VARIANT}}"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
mkdir -p "$OUT" .lake/build/lib/lean/PrimalitySheafVerification

# Commit-capable jobs must have an identity even though candidate jobs do not push.
git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

echo "variant=$VARIANT" > "$OUT/JOB_CONTEXT.txt"
echo "repository=${GITHUB_REPOSITORY:-}" >> "$OUT/JOB_CONTEXT.txt"
echo "run_id=${GITHUB_RUN_ID:-}" >> "$OUT/JOB_CONTEXT.txt"
echo "run_attempt=${GITHUB_RUN_ATTEMPT:-}" >> "$OUT/JOB_CONTEXT.txt"
echo "head_sha=${GITHUB_SHA:-$(git rev-parse HEAD)}" >> "$OUT/JOB_CONTEXT.txt"
echo "head_ref=${GITHUB_REF:-}" >> "$OUT/JOB_CONTEXT.txt"

# 1. Recover the exact authoritative baseline from fetched history.
python3 scripts/fa442_restore_authoritative_baseline.py --output-dir "$OUT" \
  > "$OUT/baseline-recovery.log" 2>&1
recover_rc=$?
printf '%s' "$recover_rc" > "$OUT/baseline-recovery.exit"
cat "$OUT/baseline-recovery.log"

# 2. Generate candidate from the recovered baseline. Never turn failure into a fake pass.
prepare_rc=125
if test "$recover_rc" -eq 0; then
  python3 scripts/fa444_prepare_same_height_candidate.py \
    --variant "$VARIANT" --output-dir "$OUT" \
    > "$OUT/prepare.log" 2>&1
  prepare_rc=$?
else
  printf 'authoritative baseline recovery failed; candidate generation not possible\n' \
    > "$OUT/prepare.log"
fi
printf '%s' "$prepare_rc" > "$OUT/prepare.exit"
cat "$OUT/prepare.log"

# 3. Install the pinned toolchain and restore the Mathlib cache in every matrix job.
curl --retry 5 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -o /tmp/elan-init.sh > "$OUT/elan-download.log" 2>&1
curl_rc=$?
printf '%s' "$curl_rc" > "$OUT/elan-download.exit"
install_rc=125
if test "$curl_rc" -eq 0; then
  sh /tmp/elan-init.sh -y --default-toolchain none \
    > "$OUT/elan-init.log" 2>&1
  elan_init_rc=$?
  printf '%s' "$elan_init_rc" > "$OUT/elan-init.exit"
  if test "$elan_init_rc" -eq 0; then
    export PATH="${HOME}/.elan/bin:${PATH}"
    elan toolchain install "$(cat lean-toolchain)" \
      > "$OUT/toolchain-install.log" 2>&1
    install_rc=$?
  fi
fi
printf '%s' "$install_rc" > "$OUT/toolchain-install.exit"
export PATH="${HOME}/.elan/bin:${PATH}"

cache_rc=125
if test "$install_rc" -eq 0; then
  lean --version > "$OUT/lean-version.txt" 2>&1
  printf '%s' "$?" > "$OUT/lean-version.exit"
  lake --version > "$OUT/lake-version.txt" 2>&1
  printf '%s' "$?" > "$OUT/lake-version.exit"
  lake exe cache get > "$OUT/cache-get.log" 2>&1
  cache_rc=$?
else
  printf 'toolchain installation failed\n' > "$OUT/cache-get.log"
fi
printf '%s' "$cache_rc" > "$OUT/cache-get.exit"
cat "$OUT/lean-version.txt" 2>/dev/null || true
cat "$OUT/lake-version.txt" 2>/dev/null || true
cat "$OUT/cache-get.log" 2>/dev/null || true

compile_one() {
  local stem="$1"
  local src="PrimalitySheafVerification/${stem}.lean"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  rm -f "$o" "$i"
  local command=(lake env lean "-DmaxErrors=${MAX_ERRORS}" -DwarningAsError=false \
    -o "$o" -i "$i" "$src")
  printf '%q ' "${command[@]}" > "$OUT/${stem}.command"
  printf '\n' >> "$OUT/${stem}.command"
  touch "$OUT/${stem}.executed"
  "${command[@]}" > "$OUT/${stem}.log" 2>&1
  local rc=$?
  printf '%s' "$rc" > "$OUT/${stem}.exit"
  if test "$rc" -eq 0 && test -s "$o" && test -s "$i"; then
    printf 'true\n' > "$OUT/${stem}.artifacts_ok"
  else
    printf 'false\n' > "$OUT/${stem}.artifacts_ok"
  fi
  return 0
}

# 4. Every valid candidate job actually invokes all three direct Lean CLI commands.
if test "$prepare_rc" -eq 0 && test "$install_rc" -eq 0 && test "$cache_rc" -eq 0; then
  compile_one Mock2
  compile_one Mock2_Advanced
  compile_one Mock2_FunctionalAnalysis
else
  for stem in Mock2 Mock2_Advanced Mock2_FunctionalAnalysis; do
    printf 'direct Lean CLI unavailable: recover=%s prepare=%s install=%s cache=%s\n' \
      "$recover_rc" "$prepare_rc" "$install_rc" "$cache_rc" > "$OUT/${stem}.log"
    printf '125' > "$OUT/${stem}.exit"
  done
fi

# 5. Produce an execution-authoritative metric even for infrastructure failures.
export FA442_OUT_DIR="$OUT"
export FA442_SOURCE="$SRC"
export FA442_METADATA="$OUT/CANDIDATE.json"
export MAX_ERRORS
python3 scripts/fa442_record_direct_metric.py \
  > "$OUT/metric-console.log" 2>&1
metric_rc=$?
printf '%s' "$metric_rc" > "$OUT/metric.exit"
cat "$OUT/metric-console.log"

# Upload/enforcement steps decide job status after evidence is preserved.
exit 0
