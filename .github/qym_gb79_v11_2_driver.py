#!/usr/bin/env python3
from pathlib import Path
import collections,hashlib,json,os,re,shutil,subprocess,sys
QYM=Path('PrimalitySheafVerification/QYM.lean'); OUT=Path('/tmp/qym-gb79-v11-2'); EDGE=Path('.github/qym_patch_v11_edgeparametertransport.py'); NORMAL=Path('.github/qym_patch_v12_complexnormal.py')
BASE_SHA='790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421'; BASE_BLOB='33e4fab1130e4c17ea5d212fe2691c3e0c0eb8d3'; BASE_ERRORS=79
EV=('letI_simpa','letI_change','transparent_simpa'); NV=('factor_normsq','generalize_normsq','cases_components')
D=re.compile(r'^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$',re.M); P=re.compile(r'(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$')
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def comp(src,label,phase,maxe):
 shutil.copy2(src,QYM); log=OUT/f'{label}.{phase}.log'; o=OUT/f'{label}.{phase}.olean'; i=OUT/f'{label}.{phase}.ilean'
 with log.open('wb') as h:q=subprocess.run(['lake','env','lean',f'-DmaxErrors={maxe}','-DwarningAsError=false','-o',str(o),'-i',str(i),str(QYM)],stdout=h,stderr=subprocess.STDOUT)
 t=log.read_text(errors='replace');rows=[]
 for m in D.finditer(t):d=m.groupdict();d['line']=int(d['line']);d['column']=int(d['column']);rows.append(d)
 es=[x for x in rows if x['severity']=='error'];ws=[x for x in rows if x['severity']=='warning'];raw=Path(src).read_bytes();r={'variant':label,'phase':phase,'exit':q.returncode,'error_headers':len(es),'warning_headers':len(ws),'panic_lines':len(P.findall(t)),'first_error':es[0] if es else None,'last_error':es[-1] if es else None,'error_codes':dict(sorted(collections.Counter((x.get('code') or 'uncoded') for x in es).items())),'candidate_qym_sha256':sha(raw),'candidate_qym_blob':blob(raw),'log_sha256':sha(log.read_bytes()),'olean_exists':o.exists() and o.stat().st_size>0,'ilean_exists':i.exists() and i.stat().st_size>0};dump(OUT/f'{label}.{phase}.json',r);return r
def patch(patcher,v,src,outjson,expected=None):
 cmd=[sys.executable,'-B',str(patcher),v,str(src)]+([expected] if expected else [])
 with Path(outjson).open('wb') as h:subprocess.run(cmd,check=True,stdout=h)
 return json.loads(Path(outjson).read_text())
def main():
 OUT.mkdir(parents=True,exist_ok=True);base=OUT/'QYM.GB79.lean';shutil.copy2(QYM,base);raw=base.read_bytes()
 if sha(raw)!=BASE_SHA or blob(raw)!=BASE_BLOB:raise SystemExit('not exact GB79')
 edge_rows=[];combo_rows=[]
 try:
  for e in EV:
   c=OUT/f'QYM.edge-{e}.lean';shutil.copy2(base,c);ep=patch(EDGE,e,c,OUT/f'edge-{e}.patch.json',BASE_SHA);local=comp(c,f'edge-{e}','local',1);first=(local.get('first_error') or {}).get('line') or 10**9;ok=local['panic_lines']==0 and first>=ep['gate_line'];edge_rows.append({'edge_variant':e,'candidate':str(c),'patch':ep,'local':local,'local_gate_pass':ok})
  for er in [x for x in edge_rows if x['local_gate_pass']]:
   for n in NV:
    label=f"{er['edge_variant']}__{n}";c=OUT/f'QYM.combo-{label}.lean';shutil.copy2(Path(er['candidate']),c);np=patch(NORMAL,n,c,OUT/f'{label}.normal.patch.json');local=comp(c,label,'local',1);first=(local.get('first_error') or {}).get('line') or 10**9;ok=local['panic_lines']==0 and first>=np['gate_line'];combo_rows.append({'variant':label,'edge_variant':er['edge_variant'],'normal_variant':n,'candidate':str(c),'normal_patch':np,'local':local,'local_gate_pass':ok})
  full=[]
  for r in [x for x in combo_rows if x['local_gate_pass']]:
   f=comp(Path(r['candidate']),r['variant'],'full',10000);f['baseline_error_headers']=BASE_ERRORS;f['run_id']=os.environ.get('GITHUB_RUN_ID');f['trigger_sha']=os.environ.get('GITHUB_SHA');f['semantic_pass']=f['exit']==0 and f['error_headers']==0 and f['panic_lines']==0 and f['olean_exists'] and f['ilean_exists'];f['strict_improvement']=f['semantic_pass'] or (f['panic_lines']==0 and f['error_headers']<BASE_ERRORS);dump(OUT/f"{r['variant']}.FULL_RESULT.json",f);r['full']=f;full.append(r)
  good=[r for r in full if r['full']['strict_improvement']];sel={'schema':'qym-gb79-v11-2-selection-v1','baseline_errors':BASE_ERRORS,'baseline_sha256':BASE_SHA,'edge_candidates':edge_rows,'combo_candidates':combo_rows,'strict_improvement_found':bool(good)}
  if good:
   good.sort(key=lambda r:(r['full']['error_headers'],r['full']['panic_lines'],-((r['full'].get('first_error') or {}).get('line') or 0),r['variant']));b=good[0];sel['best_variant']=b['variant'];sel['best']=b['full'];shutil.copy2(Path(b['candidate']),OUT/'QYM.best.lean');dump(OUT/'BEST_RESULT.json',b['full']);dump(OUT/'SELECTION.json',sel);return 0
  dump(OUT/'SELECTION.json',sel);return 2
 finally:shutil.copy2(base,QYM)
if __name__=='__main__':raise SystemExit(main())
