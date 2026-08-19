#!/usr/bin/env python3
from pathlib import Path
import collections, hashlib, json, os, re, shutil, subprocess, sys

QYM=Path("PrimalitySheafVerification/QYM.lean")
OUT=Path("/tmp/qym-gb79-v12")
P1=Path(".github/qym_gb79_v11_patch.py")
P2=Path(".github/qym_gb79_v12_groupoid_patch.py")
BASE_SHA256="790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421"
BASE_ERRORS=79
VARIANTS=("simpa_direct","change_direct","change_structural")
DIAG=re.compile(r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",re.M)
PANIC=re.compile(r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$")

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x): Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+"\n")

def compile(src,v,phase,maxerr):
    shutil.copy2(src,QYM)
    log=OUT/f"{v}.{phase}.log"; olean=OUT/f"{v}.{phase}.olean"; ilean=OUT/f"{v}.{phase}.ilean"
    cmd=["/usr/bin/time","-v","-o",str(OUT/f"{v}.{phase}.time"),"lake","env","lean",f"-DmaxErrors={maxerr}","-DwarningAsError=false","-o",str(olean),"-i",str(ilean),str(QYM)]
    with log.open("wb") as h: p=subprocess.run(cmd,stdout=h,stderr=subprocess.STDOUT)
    text=log.read_text(errors="replace"); rows=[]
    for m in DIAG.finditer(text):
        d=m.groupdict(); d["line"]=int(d["line"]); d["column"]=int(d["column"]); rows.append(d)
    es=[x for x in rows if x["severity"]=="error"]; ws=[x for x in rows if x["severity"]=="warning"]
    r={"variant":v,"phase":phase,"exit":p.returncode,"error_headers":len(es),"warning_headers":len(ws),"panic_lines":len(PANIC.findall(text)),
       "first_error":es[0] if es else None,"last_error":es[-1] if es else None,"error_codes":dict(collections.Counter((x.get("code") or "uncoded") for x in es)),
       "log_sha256":hashlib.sha256(log.read_bytes()).hexdigest(),"candidate_qym_sha256":sha(src),"olean_exists":olean.exists() and olean.stat().st_size>0,"ilean_exists":ilean.exists() and ilean.stat().st_size>0}
    dump(OUT/f"{v}.{phase}.json",r); return r

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    original=OUT/"QYM.GB79.lean"; shutil.copy2(QYM,original)
    if sha(original)!=BASE_SHA256: raise SystemExit("branch QYM is not exact GB79 authority")
    candidates=[]
    try:
        for v in VARIANTS:
            c=OUT/f"QYM.candidate-{v}.lean"; shutil.copy2(original,c)
            with (OUT/f"{v}.EDGE_NORMAL_PATCH.json").open("wb") as h:
                subprocess.run([sys.executable,"-B",str(P1),v,str(c)],check=True,stdout=h)
            with (OUT/f"{v}.GROUPOID_PATCH.json").open("wb") as h:
                subprocess.run([sys.executable,"-B",str(P2),str(c)],check=True,stdout=h)
            local=compile(c,v,"local",8)
            first=(local.get("first_error") or {}).get("line") or 10**9
            gate=local["panic_lines"]==0 and first>45526
            candidates.append({"variant":v,"candidate":str(c),"local":local,"local_gate_pass":gate})
        viable=[x for x in candidates if x["local_gate_pass"]]
        viable.sort(key=lambda x:-((x["local"].get("first_error") or {}).get("line") or 10**9))
        fulls=[]
        for x in viable[:2]:
            f=compile(Path(x["candidate"]),x["variant"],"full",10000)
            f["baseline_error_headers"]=BASE_ERRORS
            f["semantic_pass"]=f["exit"]==0 and f["error_headers"]==0 and f["panic_lines"]==0 and f["olean_exists"] and f["ilean_exists"]
            f["strict_improvement"]=f["semantic_pass"] or (f["panic_lines"]==0 and f["error_headers"]<BASE_ERRORS)
            f["run_id"]=os.environ.get("GITHUB_RUN_ID"); f["trigger_sha"]=os.environ.get("GITHUB_SHA")
            dump(OUT/f"{x['variant']}.FULL_RESULT.json",f); x["full"]=f; fulls.append(x)
        improved=[x for x in fulls if x["full"]["strict_improvement"]]
        sel={"baseline_errors":BASE_ERRORS,"baseline_sha256":BASE_SHA256,"candidates":candidates,"strict_improvement_found":bool(improved)}
        if improved:
            improved.sort(key=lambda x:(x["full"]["error_headers"],-((x["full"].get("first_error") or {}).get("line") or 0)))
            b=improved[0]; sel["best_variant"]=b["variant"]; sel["best"]=b["full"]
            shutil.copy2(Path(b["candidate"]),OUT/"QYM.best.lean"); dump(OUT/"BEST_RESULT.json",b["full"]); dump(OUT/"SELECTION.json",sel); return 0
        dump(OUT/"SELECTION.json",sel); return 2
    finally:
        shutil.copy2(original,QYM)

if __name__=="__main__": raise SystemExit(main())
