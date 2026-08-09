#!/usr/bin/env bash
set -euo pipefail
VARIANT=${1:?variant required}; export VARIANT
TARGET='PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
OUT="build-logs/fa429-convert-structure/${VARIANT}"; export OUT
rm -rf "$OUT"; mkdir -p "$OUT" .lake/build/lib/lean/PrimalitySheafVerification
python3 scripts/fa429_apply_convert_structure.py "$VARIANT" | tee "$OUT/apply.log"
curl --retry 5 --retry-all-errors --fail --silent --show-error https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none
export PATH="${HOME}/.elan/bin:${PATH}"; elan toolchain install "$(cat lean-toolchain)"
lean --version | tee "$OUT/lean-version.txt"; lake --version | tee "$OUT/lake-version.txt"; lake exe cache get | tee "$OUT/cache-get.log"
cp "$TARGET" "$OUT/candidate.lean"
compile_one(){ local stem=$1 max=$2 src="PrimalitySheafVerification/${1}.lean" o=".lake/build/lib/lean/PrimalitySheafVerification/${1}.olean" i=".lake/build/lib/lean/PrimalitySheafVerification/${1}.ilean"; rm -f "$o" "$i"; lake env lean -DmaxErrors="$max" -DwarningAsError=false -o "$o" -i "$i" "$src" > "$OUT/${stem}.log" 2>&1; local rc=$?; printf '%s' "$rc" > "$OUT/${stem}.exit"; test "$rc" -eq 0 && test -s "$o" && test -s "$i"; }
set +e; compile_one Mock2 20; rc_m2=$?; compile_one Mock2_Advanced 20; rc_m2a=$?; rc_fa=125
if test "$rc_m2" -eq 0 && test "$rc_m2a" -eq 0; then compile_one Mock2_FunctionalAnalysis 20; rc_fa=$?; else printf 'blocked by prerequisite regression\n' > "$OUT/Mock2_FunctionalAnalysis.log"; printf '%s' "$rc_fa" > "$OUT/Mock2_FunctionalAnalysis.exit"; fi
set -e; export RC_M2="$rc_m2" RC_M2A="$rc_m2a" RC_FA="$rc_fa"
python3 - <<'PY'
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
sys.path.insert(0,str(Path('scripts').resolve())); import fa422_canonical_decl_tournament as engine
v=os.environ['VARIANT']; out=Path(os.environ['OUT']); src=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'); cand=src.read_text(); base=subprocess.check_output(['git','show','HEAD:PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'],text=True)
bsha=hashlib.sha256(base.encode()).hexdigest(); csha=hashlib.sha256(cand.encode()).hexdigest(); log=(out/'Mock2_FunctionalAnalysis.log').read_text(errors='replace'); pat=re.compile(r'Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+(?:error(?:\([^)]*\))?:|error:)'); ms=list(pat.finditer(log)); first=int(ms[0].group(1)) if ms else None; col=int(ms[0].group(2)) if ms else None
m2=int(os.environ['RC_M2']); m2a=int(os.environ['RC_M2A']); fa=int(os.environ['RC_FA']); idx=engine.decl_index_at(cand,first); baseidx=2658
better=fa==0 or (isinstance(first,int) and first>31726 and isinstance(idx,int) and (idx>baseidx or (idx==baseidx and len(cand.splitlines())==len(base.splitlines()))))
stmt=engine.manifest(cand)==engine.manifest(base); imports=engine.core.imports(cand)==engine.core.imports(base); forbidden=engine.core.forbidden_hits(cand); auth=bsha=='71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0' and m2==0 and m2a==0 and better and stmt and imports and not any(forbidden.values())
status={'classification':'VERIFIED' if auth else 'CANDIDATE_REJECTED','variant':v,'baseline_sha256':bsha,'candidate_sha256':csha,'baseline_line_count':len(base.splitlines()),'candidate_line_count':len(cand.splitlines()),'Mock2_exit':m2,'Mock2_Advanced_exit':m2a,'FA_exit':fa,'FA_error_headers_captured':len(ms),'FA_first_actual_error_line':first,'FA_first_actual_error_col':col,'FA_error_declaration_index':idx,'baseline_declaration_index':baseidx,'maxErrors_cap':20,'strictly_better':better,'authorized_for_materialization':auth,'statement_manifest_unchanged':stmt,'imports_unchanged':imports,'forbidden_token_audit':forbidden}
(out/'CURRENT.json').write_text(json.dumps(status,indent=2)+'\n'); (out/'CURRENT.txt').write_text('\n'.join(f'{k}={x}' for k,x in status.items())+'\n'); (out/('AUTHORIZED' if auth else 'REJECTED')).touch(); (out/'FINAL_EXIT').write_text('0' if auth else '1'); print(json.dumps(status,indent=2))
PY
