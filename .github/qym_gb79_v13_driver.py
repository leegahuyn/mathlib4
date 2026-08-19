#!/usr/bin/env python3
from pathlib import Path
import collections, hashlib, itertools, json, os, re, shutil, subprocess, sys

QYM=Path('PrimalitySheafVerification/QYM.lean')
OUT=Path('/tmp/qym-gb79-v13')
V11=Path('.github/qym_gb79_v11_patch.py')
V12=Path('.github/qym_gb79_v12_patch.py')
C08=Path('.github/qym_gb79_v13_c08_patch.py')
BASE_SHA256='790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421'
BASE_BLOB='33e4fab1130e4c17ea5d212fe2691c3e0c0eb8d3'
BASE_ERRORS=79
COMBOS=[(a,b) for a in ('syntax_only','syntax_algebra') for b in ('dense_induction','explicit_args')]
DIAG=re.compile(r'^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$',re.M)
PANIC=re.compile(r'(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$')
def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def dump(p,x): Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')

def compile(src,label,phase,maxerr):
  shutil.copy2(src,QYM); log=OUT/f'{label}.{phase}.log'; o=OUT/f'{label}.{phase}.olean'; i=OUT/f'{label}.{phase}.ilean'
  with log.open('wb') as h:
    p=subprocess.run(['lake','env','lean',f'-DmaxErrors={maxerr}','-DwarningAsError=false','-o',str(o),'-i',str(i),str(QYM)],stdout=h,stderr=subprocess.STDOUT)
  text=log.read_text(errors='replace'); rows=[]
  for m in DIAG.finditer(text):
    d=m.groupdict(); d['line']=int(d['line']); d['column']=int(d['column']); rows.append(d)
  es=[x for x in rows if x['severity']=='error']; ws=[x for x in rows if x['severity']=='warning']; raw=Path(src).read_bytes()
  r={'variant':label,'phase':phase,'exit':p.returncode,'error_headers':len(es),'warning_headers':len(ws),'panic_lines':len(PANIC.findall(text)),'first_error':es[0] if es else None,'last_error':es[-1] if es else None,'error_codes':dict(sorted(collections.Counter((x.get('code') or 'uncoded') for x in es).items())),'candidate_qym_sha256':sha(raw),'candidate_qym_blob':blob(raw),'log_sha256':sha(log.read_bytes()),'olean_exists':o.exists() and o.stat().st_size>0,'ilean_exists':i.exists() and i.stat().st_size>0}
  dump(OUT/f'{label}.{phase}.json',r); return r

def main():
  OUT.mkdir(parents=True,exist_ok=True); original=OUT/'QYM.GB79.lean'; shutil.copy2(QYM,original); raw=original.read_bytes()
  if sha(raw)!=BASE_SHA256 or blob(raw)!=BASE_BLOB: raise SystemExit('not exact GB79 source')
  rows=[]
  try:
    for v12,c08 in COMBOS:
      label=f'{v12}__{c08}'; c=OUT/f'QYM.candidate-{label}.lean'; shutil.copy2(original,c)
      with (OUT/f'{label}.v11.json').open('wb') as h: subprocess.run([sys.executable,'-B',str(V11),'first13',str(c)],check=True,stdout=h)
      with (OUT/f'{label}.v12.json').open('wb') as h: subprocess.run([sys.executable,'-B',str(V12),v12,str(c)],check=True,stdout=h)
      with (OUT/f'{label}.c08.json').open('wb') as h: subprocess.run([sys.executable,'-B',str(C08),c08,str(c)],check=True,stdout=h)
      pc08=json.loads((OUT/f'{label}.c08.json').read_text())
      local=compile(c,label,'local',1); first=(local.get('first_error') or {}).get('line') or 10**9
      ok=local['panic_lines']==0 and int(first)>=int(pc08['gate_line'])
      rows.append({'variant':label,'v12_variant':v12,'c08_variant':c08,'candidate':str(c),'c08_patch':pc08,'local':local,'local_gate_pass':ok})
    viable=[r for r in rows if r['local_gate_pass']]; fullrows=[]
    for r in viable:
      f=compile(Path(r['candidate']),r['variant'],'full',10000); f['baseline_error_headers']=BASE_ERRORS; f['run_id']=os.environ.get('GITHUB_RUN_ID'); f['trigger_sha']=os.environ.get('GITHUB_SHA'); f['semantic_pass']=f['exit']==0 and f['error_headers']==0 and f['panic_lines']==0 and f['olean_exists'] and f['ilean_exists']; f['strict_improvement']=f['semantic_pass'] or (f['panic_lines']==0 and f['error_headers']<BASE_ERRORS); dump(OUT/f"{r['variant']}.FULL_RESULT.json",f); r['full']=f; fullrows.append(r)
    improved=[r for r in fullrows if r['full']['strict_improvement']]; sel={'schema':'qym-gb79-v13-selection-v1','baseline':{'errors':BASE_ERRORS,'sha256':BASE_SHA256,'blob':BASE_BLOB},'candidates':rows,'strict_improvement_found':bool(improved)}
    if improved:
      improved.sort(key=lambda r:(r['full']['error_headers'],r['full']['panic_lines'],-((r['full'].get('first_error') or {}).get('line') or 0),r['variant'])); b=improved[0]; sel['best_variant']=b['variant']; sel['best']=b['full']; shutil.copy2(Path(b['candidate']),OUT/'QYM.best.lean'); dump(OUT/'BEST_RESULT.json',b['full']); dump(OUT/'SELECTION.json',sel); return 0
    dump(OUT/'SELECTION.json',sel); return 2
  finally: shutil.copy2(original,QYM)
if __name__=='__main__': raise SystemExit(main())
