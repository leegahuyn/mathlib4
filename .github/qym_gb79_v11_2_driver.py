#!/usr/bin/env python3
from pathlib import Path
import collections, hashlib, json, os, re, shutil, subprocess, sys

QYM=Path('PrimalitySheafVerification/QYM.lean')
OUT=Path('/tmp/qym-gb79-v11-2')
BASE_SHA='790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421'
BASE_BLOB='33e4fab1130e4c17ea5d212fe2691c3e0c0eb8d3'
BASE_ERRORS=79
DIAG=re.compile(r'^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$',re.M)
PANIC=re.compile(r'(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$')

def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def dump(p,x): Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')

def compile(src,phase,max_errors):
    shutil.copy2(src,QYM)
    log=OUT/f'cumulative.{phase}.log'; olean=OUT/f'cumulative.{phase}.olean'; ilean=OUT/f'cumulative.{phase}.ilean'
    with log.open('wb') as h:
        proc=subprocess.run(['lake','env','lean',f'-DmaxErrors={max_errors}','-DwarningAsError=false','-o',str(olean),'-i',str(ilean),str(QYM)],stdout=h,stderr=subprocess.STDOUT)
    text=log.read_text(errors='replace'); rows=[]
    for m in DIAG.finditer(text):
        d=m.groupdict(); d['line']=int(d['line']); d['column']=int(d['column']); rows.append(d)
    es=[x for x in rows if x['severity']=='error']; ws=[x for x in rows if x['severity']=='warning']
    r={'phase':phase,'exit':proc.returncode,'error_headers':len(es),'warning_headers':len(ws),'panic_lines':len(PANIC.findall(text)),
       'first_error':es[0] if es else None,'last_error':es[-1] if es else None,
       'error_codes':dict(sorted(collections.Counter((x.get('code') or 'uncoded') for x in es).items())),
       'log_sha256':sha(log.read_bytes()),'candidate_qym_sha256':sha(Path(src).read_bytes()),'candidate_qym_blob':blob(Path(src).read_bytes()),
       'olean_exists':olean.is_file() and olean.stat().st_size>0,'ilean_exists':ilean.is_file() and ilean.stat().st_size>0}
    dump(OUT/f'{phase}.json',r); return r

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    original=OUT/'QYM.GB79.lean'; shutil.copy2(QYM,original); raw=original.read_bytes()
    check={'sha_ok':sha(raw)==BASE_SHA,'blob_ok':blob(raw)==BASE_BLOB,'sha256':sha(raw),'blob':blob(raw),'error_headers':BASE_ERRORS}
    dump(OUT/'BASELINE_CHECK.json',check)
    if not check['sha_ok'] or not check['blob_ok']: raise SystemExit(f'GB79 mismatch {check}')
    cand=OUT/'QYM.candidate-edge-normal-atlas.lean'; shutil.copy2(original,cand)
    try:
        with (OUT/'EDGE_NORMAL_PATCH.json').open('wb') as h:
            subprocess.run([sys.executable,'-B','.github/qym_patch_gb79_v11_1.py','edge_both',str(cand)],check=True,stdout=h)
        with (OUT/'ATLAS_PATCH.json').open('wb') as h:
            subprocess.run([sys.executable,'-B','.github/qym_patch_v11_2_atlas.py',str(cand)],check=True,stdout=h)
        atlas=json.loads((OUT/'ATLAS_PATCH.json').read_text())
        local=compile(cand,'local',1); gate=int(atlas['gate_line']); first=int((local.get('first_error') or {}).get('line') or 10**9)
        local['gate_line']=gate; local['gate_pass']=int(local['panic_lines'])==0 and first>=gate; dump(OUT/'LOCAL_RESULT.json',local)
        if not local['gate_pass']:
            dump(OUT/'SELECTION.json',{'schema':'qym-gb79-v11-2-selection-v1','baseline':check,'local':local,'strict_improvement_found':False})
            return 2
        full=compile(cand,'full',10000)
        semantic=int(full['exit'])==0 and int(full['error_headers'])==0 and int(full['panic_lines'])==0 and full['olean_exists'] and full['ilean_exists']
        strict=semantic or (int(full['panic_lines'])==0 and int(full['error_headers'])<BASE_ERRORS)
        full.update({'semantic_pass':semantic,'strict_improvement':strict,'baseline_error_headers':BASE_ERRORS,'baseline_qym_sha256':BASE_SHA,'baseline_qym_blob':BASE_BLOB,'run_id':os.environ.get('GITHUB_RUN_ID'),'trigger_sha':os.environ.get('GITHUB_SHA')})
        dump(OUT/'FULL_RESULT.json',full)
        sel={'schema':'qym-gb79-v11-2-selection-v1','baseline':check,'local':local,'full':full,'strict_improvement_found':strict}; dump(OUT/'SELECTION.json',sel)
        if strict:
            shutil.copy2(cand,OUT/'QYM.best.lean'); dump(OUT/'BEST_RESULT.json',full); return 0
        return 2
    finally:
        shutil.copy2(original,QYM)

if __name__=='__main__': raise SystemExit(main())
