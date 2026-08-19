#!/usr/bin/env bash
set -uo pipefail

QYM="PrimalitySheafVerification/QYM.lean"
OLEAN=".lake/build/lib/lean/PrimalitySheafVerification"
OUT="/tmp/qym-probe40b"
A="${RUNNER_TEMP}/authority"
AUTH_SHA="00f2c8ba7fc0329b04ae67c5a67b5814f8118b14222a7831a0401c9d3d374e53"
AUTH_BLOB="ee2faeaf281215b0e9b304a96ccdce3e8cdc0ffb"
CANDIDATE_SHA="f1f82104eafe6cce42fc6c0db4d16a0f293f70891302a4453ba14aa8453dfcb0"
CANDIDATE_BLOB="0b20e890c0a62ae0b7b2d43f841ccfe570758ddb"

mkdir -p "$OUT" "$OLEAN"
cp "$QYM" "$OUT/QYM.canonical.lean"
sha256sum "$QYM" > "$OUT/canonical-before.sha256"
git hash-object --no-filters "$QYM" > "$OUT/canonical-before.blob"

restore_canonical() {
  if [[ -f "$OUT/QYM.canonical.lean" ]]; then
    cp "$OUT/QYM.canonical.lean" "$QYM"
  fi
}
trap restore_canonical EXIT

{
  set -euo pipefail
  test "$(tr -d '\r\n' < lean-toolchain)" = "leanprover/lean4:v4.33.0-rc1"
  test -f .github/qym_probe40_full_stabilizer_patch.py
  test -f .github/qym_probe40b_horocycle_patch.py
  test -f .github/qym_probe_summarize.py

  for f in \
    QYM.candidate-probe35-flat_named.lean \
    QYM.exit QYM.error-headers.txt QYM.panic-lines.txt \
    QYM.log PROBE_RESULT.json; do
    test -f "$A/$f"
  done
  test "$(sha256sum "$A/QYM.candidate-probe35-flat_named.lean" | awk '{print $1}')" = "$AUTH_SHA"
  test "$(git hash-object --no-filters "$A/QYM.candidate-probe35-flat_named.lean")" = "$AUTH_BLOB"
  test "$(cat "$A/QYM.exit")" = "1"
  test "$(wc -l < "$A/QYM.error-headers.txt")" -eq 89
  test ! -s "$A/QYM.panic-lines.txt"
  python3 - "$A/PROBE_RESULT.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1], encoding='utf-8'))
assert r['candidate_qym_sha256'] == '00f2c8ba7fc0329b04ae67c5a67b5814f8118b14222a7831a0401c9d3d374e53'
assert r['candidate_qym_blob'] == 'ee2faeaf281215b0e9b304a96ccdce3e8cdc0ffb'
assert r['exit'] == 1
assert r['error_headers'] == 89
assert r['panic_lines'] == 0
PY
  cp "$A/QYM.candidate-probe35-flat_named.lean" "$OUT/QYM.authority.lean"
  cp "$A/PROBE_RESULT.json" "$OUT/AUTHORITY_RESULT.json"
  cp "$A/QYM.log" "$OUT/QYM.authority.log"

  curl --retry 5 --retry-all-errors --fail --silent --show-error \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan.sh
  sh /tmp/elan.sh -y --default-toolchain none > "$OUT/elan.log" 2>&1
  export PATH="$HOME/.elan/bin:$PATH"
  echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
  elan toolchain install "$(tr -d '\r\n' < lean-toolchain)" > "$OUT/toolchain.log" 2>&1
  lake exe cache get > "$OUT/mathlib-cache.log" 2>&1
  lean --version | tee "$OUT/lean-version.txt"
  lake --version | tee "$OUT/lake-version.txt"

  for stem in Mock2 Mock2_Advanced Mock2_FunctionalAnalysis Mock2_FunctionalAnalysis_Integrated; do
    if [[ ! -s "$OLEAN/$stem.olean" || ! -s "$OLEAN/$stem.ilean" ]]; then
      cap=1
      if [[ "$stem" = Mock2_FunctionalAnalysis || "$stem" = Mock2_FunctionalAnalysis_Integrated ]]; then
        cap=2000
      fi
      rm -f "$OLEAN/$stem.olean" "$OLEAN/$stem.ilean"
      lake env lean "-DmaxErrors=$cap" -DwarningAsError=false \
        -o "$OLEAN/$stem.olean" -i "$OLEAN/$stem.ilean" \
        "PrimalitySheafVerification/$stem.lean" > "$OUT/$stem.log" 2>&1
    fi
    test -s "$OLEAN/$stem.olean"
    test -s "$OLEAN/$stem.ilean"
  done

  cp "$OUT/QYM.authority.lean" "$QYM"
  python3 -B .github/qym_probe40_full_stabilizer_patch.py \
    "$QYM" "$OUT/STABILIZER_PATCH_RESULT.json" \
    > "$OUT/STABILIZER_PATCH_RESULT.stdout.json"
  python3 -B .github/qym_probe40b_horocycle_patch.py \
    "$QYM" "$OUT/PATCH_RESULT.json" \
    > "$OUT/PATCH_RESULT.stdout.json"
  test "$(sha256sum "$QYM" | awk '{print $1}')" = "$CANDIDATE_SHA"
  test "$(git hash-object --no-filters "$QYM")" = "$CANDIDATE_BLOB"
  cp "$QYM" "$OUT/QYM.candidate.lean"
  sha256sum "$QYM" > "$OUT/QYM.candidate.sha256"
  git hash-object --no-filters "$QYM" > "$OUT/QYM.candidate.blob"

  printf '%q ' lake env lean -DmaxErrors=10000 -DwarningAsError=false \
    -o "$RUNNER_TEMP/QYM.probe40b.olean" \
    -i "$RUNNER_TEMP/QYM.probe40b.ilean" "$QYM" > "$OUT/QYM.command"
  printf '\n' >> "$OUT/QYM.command"

  set +e
  /usr/bin/time -v -o "$OUT/QYM.time" \
    lake env lean -DmaxErrors=10000 -DwarningAsError=false \
      -o "$RUNNER_TEMP/QYM.probe40b.olean" \
      -i "$RUNNER_TEMP/QYM.probe40b.ilean" \
      "$QYM" > "$OUT/QYM.log" 2>&1
  rc=$?
  set -e
  echo "$rc" > "$OUT/QYM.exit"
  if [[ "$rc" -eq 0 ]]; then
    test -s "$RUNNER_TEMP/QYM.probe40b.olean"
    test -s "$RUNNER_TEMP/QYM.probe40b.ilean"
    cp "$RUNNER_TEMP/QYM.probe40b.olean" "$OUT/QYM.olean"
    cp "$RUNNER_TEMP/QYM.probe40b.ilean" "$OUT/QYM.ilean"
    sha256sum "$OUT/QYM.olean" "$OUT/QYM.ilean" > "$OUT/QYM.outputs.sha256"
  fi

  python3 -B .github/qym_probe_summarize.py \
    "$OUT" "qym-probe40b-stabilizer-horocycle-v2" \
    "$CANDIDATE_SHA" "$CANDIDATE_BLOB" "$AUTH_SHA"
  python3 - "$OUT/PROBE_RESULT.json" <<'PY'
import json, os, sys
p = sys.argv[1]
r = json.load(open(p, encoding='utf-8'))
r['authority_run_id'] = 32095253829
r['authority_artifact'] = 'qym-probe35-flat_named-da2958a421605d9b267afdce59990ec19c1be10f-attempt1'
r['baseline_error_headers'] = 89
patch = json.load(open(os.path.join(os.path.dirname(p), 'PATCH_RESULT.json'), encoding='utf-8'))
r['bytes'] = patch['bytes']
r['lf'] = patch['lf']
with open(p, 'w', encoding='utf-8') as f:
    json.dump(r, f, indent=2, sort_keys=True)
    f.write('\n')
print(json.dumps(r, indent=2, sort_keys=True))
PY
} > "$OUT/driver.stdout.log" 2> "$OUT/driver.stderr.log"
status=$?

restore_canonical
trap - EXIT

if [[ -f "$OUT/PROBE_RESULT.json" ]]; then
  cat "$OUT/PROBE_RESULT.json"
fi

test "$(sha256sum "$QYM" | awk '{print $1}')" = "$(awk '{print $1}' "$OUT/canonical-before.sha256")"
test "$(git hash-object --no-filters "$QYM")" = "$(cat "$OUT/canonical-before.blob")"
test -z "$(git status --porcelain=v1 --untracked-files=all)"
exit "$status"
