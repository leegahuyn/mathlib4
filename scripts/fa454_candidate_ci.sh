#!/usr/bin/env bash
set +e

: "${VARIANT:?VARIANT is required}"
OUT="build-logs/fa454-cumulative/candidates/${VARIANT}"
SRC="PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
MAX_ERRORS="${MAX_ERRORS:-120}"
rm -rf "$OUT"
mkdir -p "$OUT" .lake/build/lib/lean/PrimalitySheafVerification

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
git rev-parse HEAD > "$OUT/repository-head.txt"
cp "$SRC" "$OUT/checked-in-baseline.lean"
sha256sum "$SRC" | awk '{print $1}' > "$OUT/checked-in-baseline.sha256"
wc -l < "$SRC" | tr -d ' ' > "$OUT/checked-in-baseline.lines"

# Pinned Lean and Mathlib cache are installed in every candidate job.
curl --retry 5 --retry-all-errors --fail --silent --show-error \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -o /tmp/elan-init.sh > "$OUT/elan-download.log" 2>&1
curl_rc=$?
printf '%s' "$curl_rc" > "$OUT/elan-download.exit"
install_rc=125
if test "$curl_rc" -eq 0; then
  sh /tmp/elan-init.sh -y --default-toolchain none > "$OUT/elan-init.log" 2>&1
  elan_rc=$?
  printf '%s' "$elan_rc" > "$OUT/elan-init.exit"
  if test "$elan_rc" -eq 0; then
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
  lake --version > "$OUT/lake-version.txt" 2>&1
  lake exe cache get > "$OUT/cache-get.log" 2>&1
  cache_rc=$?
else
  printf 'toolchain installation failed\n' > "$OUT/cache-get.log"
fi
printf '%s' "$cache_rc" > "$OUT/cache-get.exit"
cat "$OUT/lean-version.txt" 2>/dev/null || true
cat "$OUT/lake-version.txt" 2>/dev/null || true
cat "$OUT/cache-get.log" 2>/dev/null || true

compile_named() {
  local stem="$1"
  local label="$2"
  local cap="$3"
  local src="PrimalitySheafVerification/${stem}.lean"
  local o=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.olean"
  local i=".lake/build/lib/lean/PrimalitySheafVerification/${stem}.ilean"
  rm -f "$o" "$i"
  local command=(lake env lean "-DmaxErrors=${cap}" -DwarningAsError=false \
    -o "$o" -i "$i" "$src")
  printf '%q ' "${command[@]}" > "$OUT/${label}.command"
  printf '\n' >> "$OUT/${label}.command"
  touch "$OUT/${label}.executed"
  "${command[@]}" > "$OUT/${label}.log" 2>&1
  local rc=$?
  printf '%s' "$rc" > "$OUT/${label}.exit"
  local artifacts=false
  if test "$rc" -eq 0 && test -s "$o" && test -s "$i"; then
    artifacts=true
  fi
  printf '%s' "$artifacts" > "$OUT/${label}.artifacts_ok"
}

prepare_rc=125
interim_rc=125
second_rc=0
if test "$install_rc" -eq 0 && test "$cache_rc" -eq 0; then
  python3 scripts/fa454_prepare_dynamic_candidate.py \
    --variant "$VARIANT" --stage initial --output-dir "$OUT" \
    > "$OUT/prepare-initial.log" 2>&1
  prepare_rc=$?
  printf '%s' "$prepare_rc" > "$OUT/prepare-initial.exit"
  cat "$OUT/prepare-initial.log"
  if test "$prepare_rc" -eq 0; then
    # This interim compile is actual direct Lean evidence.  It determines the
    # second-stage target rather than trusting a candidate name or metadata.
    compile_named Mock2_FunctionalAnalysis interim-FA "$MAX_ERRORS"
    interim_rc=$(cat "$OUT/interim-FA.exit")
    python3 - "$OUT/interim-FA.log" "$SRC" "$OUT/INTERIM_METRIC.json" <<'PY'
import hashlib,json,re,sys
from pathlib import Path
log=Path(sys.argv[1]).read_text(encoding='utf-8',errors='replace')
source_path=Path(sys.argv[2]); text=source_path.read_text(encoding='utf-8')
out=Path(sys.argv[3])
error_re=re.compile(r'(?m)^.*Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+error:\s*(.*)$')
decl_re=re.compile(r'^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)',re.M)
matches=list(error_re.finditer(log))
line=int(matches[0].group(1)) if matches else 0
col=int(matches[0].group(2)) if matches else 0
message=matches[0].group(3) if matches else ''
name='<none>'; index=-1; start=0
for i,m in enumerate(decl_re.finditer(text)):
    decl_line=text.count('\n',0,m.start())+1
    if decl_line>line: break
    name=m.group(1); index=i; start=decl_line
result={
  'source_sha256':hashlib.sha256(source_path.read_bytes()).hexdigest(),
  'line_count':len(text.splitlines()),
  'exit':int(Path(str(sys.argv[1]).replace('.log','.exit')).read_text()),
  'first_line':line,'first_col':col,'first_message':message,
  'declaration':name,'declaration_index':index,'declaration_start':start,
  'direct_Lean_executed':Path(str(sys.argv[1]).replace('.log','.executed')).exists(),
}
out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2,ensure_ascii=False))
PY
    if [[ "$VARIANT" == compact_then_* ]] && test "$interim_rc" -ne 0; then
      readarray -t target < <(python3 - <<'PY'
import json
m=json.load(open('build-logs/fa454-cumulative/candidates/' + __import__('os').environ['VARIANT'] + '/INTERIM_METRIC.json'))
print(m['first_line'])
print(m['declaration'])
PY
)
      python3 scripts/fa454_prepare_dynamic_candidate.py \
        --variant "$VARIANT" --stage second \
        --error-line "${target[0]}" \
        --error-declaration "${target[1]}" \
        --output-dir "$OUT" \
        > "$OUT/prepare-second.log" 2>&1
      second_rc=$?
      printf '%s' "$second_rc" > "$OUT/prepare-second.exit"
      cat "$OUT/prepare-second.log"
    fi
  fi
fi

# Build final metadata from actual materialized bytes and audited invariants.
if test "$prepare_rc" -eq 0 && test "$second_rc" -eq 0; then
  python3 - "$OUT" "$SRC" <<'PY'
import hashlib,importlib.util,json,re,sys
from pathlib import Path
out=Path(sys.argv[1]); source=Path(sys.argv[2]); data=source.read_bytes(); text=data.decode('utf-8')
initial=json.loads((out/'PREPARE-initial.json').read_text(encoding='utf-8'))
second={}
if (out/'PREPARE-second.json').exists():
    second=json.loads((out/'PREPARE-second.json').read_text(encoding='utf-8'))
spec=importlib.util.spec_from_file_location('fa442_audit','scripts/fa442_prepare_same_height_candidate.py')
mod=importlib.util.module_from_spec(spec); sys.modules[spec.name]=mod
assert spec.loader is not None; spec.loader.exec_module(mod)
audit=mod.forbidden_counts(text)
metadata={
  'variant':initial['variant'],
  'baseline_sha256':'1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb',
  'candidate_sha256':hashlib.sha256(data).hexdigest(),
  'line_count':len(text.splitlines()),
  'target_declaration':'actualEdgeAmbientParam_hasDerivAt',
  'target_header_sha256':(second or initial)['authoritative_header_sha256'],
  'compact_header_sha256':(second or initial)['compact_header_sha256'],
  'declaration_sequence_sha256':(second or initial)['declaration_sequence_sha256'],
  'declaration_count':(second or initial)['declaration_count'],
  'baseline_forbidden_counts':audit if initial['variant']=='baseline' else {},
  'candidate_forbidden_counts':audit,
  'repairs':initial.get('repairs',[])+second.get('repairs',[]),
  'interim_metric':json.loads((out/'INTERIM_METRIC.json').read_text(encoding='utf-8')),
}
(out/'CANDIDATE.json').write_text(json.dumps(metadata,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
(out/'Mock2_FunctionalAnalysis-candidate.lean').write_bytes(data)
print(json.dumps(metadata,indent=2,ensure_ascii=False))
PY
fi

# Every final candidate is subjected to the same three direct Lean commands.
if test "$prepare_rc" -eq 0 && test "$second_rc" -eq 0 && \
   test "$install_rc" -eq 0 && test "$cache_rc" -eq 0; then
  compile_named Mock2 Mock2 50
  compile_named Mock2_Advanced Mock2_Advanced 50
  compile_named Mock2_FunctionalAnalysis Mock2_FunctionalAnalysis "$MAX_ERRORS"
else
  for stem in Mock2 Mock2_Advanced Mock2_FunctionalAnalysis; do
    printf '125' > "$OUT/${stem}.exit"
    printf 'final direct Lean unavailable: prepare=%s second=%s install=%s cache=%s\n' \
      "$prepare_rc" "$second_rc" "$install_rc" "$cache_rc" > "$OUT/${stem}.log"
  done
fi

export FA442_OUT_DIR="$OUT"
export FA442_SOURCE="$SRC"
export FA442_METADATA="$OUT/CANDIDATE.json"
export FA442_EXPECTED_LINES="$(wc -l < "$SRC" | tr -d ' ')"
export MAX_ERRORS
python3 scripts/fa442_record_direct_metric.py \
  > "$OUT/metric-console.log" 2>&1
metric_rc=$?
printf '%s' "$metric_rc" > "$OUT/metric.exit"
cat "$OUT/metric-console.log"
exit 0
