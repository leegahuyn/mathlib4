#!/usr/bin/env python3
from pathlib import Path
import collections, hashlib, json, os, re, shutil, subprocess, sys

QYM=Path('PrimalitySheafVerification/QYM.lean')
PATCHER=Path('.github/qym_patch_gb78_v16_timeout.py')
OUT=Path('/tmp/qym-gb78-v16-timeout')
BASE_SHA='c1498d669d3f43cda50edf7b61b33c865b00f6fe65ea95d9f1ab3c07794d1235'
BASE_BLOB='75c2eab05b4298d94246a6b0757f98a6ff5c02fe'
BASE_ERRORS=78
VARIANTS=('dense_induction','explicit_args')
DIAG=re.compile(r'^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$',re.M)
PANIC=re.compile(r'(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$')

def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def dump(p,v): Path(p).write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')

def compile_candidate(src,v):
    shutil.copy2(src,QYM); log=OUT/f'{v}.full.log'; olean=OUT/f'{v}.full.olean'; ilean=OUT/f'{v}.full.ilean'
    with log.open('wb') as h:
        proc=subprocess.run(['lake','env','lean','-DmaxErrors=10000','-DwarningAsError=false','-o',str(olean),'-i',str(ilean),str(QYM)],stdout=h,stderr=subprocess.STDOUT)
    text=log.read_text(errors='replace'); rows=[]
    for m in DIAG.finditer(text):
        d=m.groupdict(); d['line']=int(d['line']); d['column']=int(d['column']); rows.append(d)
    errors=[x for x in rows if x['severity']=='error']; warnings=[x for x in rows if x['severity']=='warning']
    result={'variant':v,'phase':'full','exit':proc.returncode,'error_headers':len(errors),'warning_headers':len(warnings),'panic_lines':len(PANIC.findall(text)),'first_error':errors[0] if errors else None,'last_error':errors[-1] if errors else None,'error_codes':dict(sorted(collections.Counter((x.get('code') or 'uncoded') for x in errors).items())),'log_sha256':sha(log.read_bytes()),'candidate_qym_sha256':sha(src.read_bytes()),'candidate_qym_blob':blob(src.read_bytes()),'olean_exists':olean.is_file() and olean.stat().st_size>0,'ilean_exists':ilean.is_file() and ilean.stat().st_size>0}
    semantic=proc.returncode==0 and not errors and result['panic_lines']==0 and result['olean_exists'] and result['ilean_exists']
    result.update({'semantic_pass':semantic,'strict_improvement':semantic or (result['panic_lines']==0 and len(errors)<BASE_ERRORS),'baseline_error_headers':BASE_ERRORS,'baseline_qym_sha256':BASE_SHA,'baseline_qym_blob':BASE_BLOB,'run_id':os.environ.get('GITHUB_RUN_ID'),'trigger_sha':os.environ.get('GITHUB_SHA')})
    dump(OUT/f'{v}.FULL_RESULT.json',result); return result

def main():
    OUT.mkdir(parents=True,exist_ok=True); original=OUT/'QYM.GB78.lean'; shutil.copy2(QYM,original); raw=original.read_bytes()
    baseline={'sha256':sha(raw),'blob':blob(raw),'errors':BASE_ERRORS,'sha_ok':sha(raw)==BASE_SHA,'blob_ok':blob(raw)==BASE_BLOB,'run_id':'32267726196','job_id':'96115476882'}; dump(OUT/'BASELINE_CHECK.json',baseline)
    if not baseline['sha_ok'] or not baseline['blob_ok']: raise SystemExit(f'authority mismatch {baseline}')
    rows=[]
    try:
        for v in VARIANTS:
            candidate=OUT/f'QYM.candidate-{v}.lean'; shutil.copy2(original,candidate); patch=OUT/f'{v}.PATCH_RESULT.json'
            with patch.open('wb') as h: subprocess.run([sys.executable,'-B',str(PATCHER),v,str(candidate),BASE_SHA],check=True,stdout=h,stderr=subprocess.STDOUT)
            result=compile_candidate(candidate,v); rows.append({'variant':v,'candidate':str(candidate),'patch':json.loads(patch.read_text()),'full':result}); dump(OUT/'PARTIAL_SELECTION.json',{'baseline':baseline,'candidates':rows})
        improved=[r for r in rows if r['full']['strict_improvement']]
        selection={'schema':'qym-gb78-v16-timeout-selection-v1','baseline':baseline,'candidates':rows,'strict_improvement_found':bool(improved)}
        if improved:
            improved.sort(key=lambda r:(r['full']['error_headers'],r['full']['panic_lines'],-int(((r['full'].get('first_error') or {}).get('line') or 0)),r['variant']))
            best=improved[0]; selection['best_variant']=best['variant']; selection['best']=best['full']; shutil.copy2(Path(best['candidate']),OUT/'QYM.best.lean'); dump(OUT/'BEST_RESULT.json',best['full']); dump(OUT/'SELECTION.json',selection); return 0
        dump(OUT/'SELECTION.json',selection); return 2
    finally: shutil.copy2(original,QYM)
if __name__=='__main__': raise SystemExit(main())
