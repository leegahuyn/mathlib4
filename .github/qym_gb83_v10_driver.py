#!/usr/bin/env python3
from pathlib import Path
import collections, hashlib, json, os, re, shutil, subprocess, sys

QYM = Path("PrimalitySheafVerification/QYM.lean")
OUT = Path("/tmp/qym-gb83-v10")
PATCHER = Path(".github/qym_gb83_v10_patch.py")
BASE_SHA256 = "ea7c26fd104104e852a6c678017b1fb0c76abb062edd758228c4bbe506dbe8d1"
BASE_ERRORS = 83
VARIANTS = ("addgroup", "addgroup_module_selected", "addgroup_module_selected_edge")
DIAG = re.compile(r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$", re.M)
PANIC = re.compile(r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$")

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x): Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+"\n")

def compile(src, variant, phase, maxerr):
    shutil.copy2(src,QYM)
    log=OUT/f"{variant}.{phase}.log"; olean=OUT/f"{variant}.{phase}.olean"; ilean=OUT/f"{variant}.{phase}.ilean"
    cmd=["lake","env","lean",f"-DmaxErrors={maxerr}","-DwarningAsError=false","-o",str(olean),"-i",str(ilean),str(QYM)]
    with log.open("wb") as h: p=subprocess.run(cmd,stdout=h,stderr=subprocess.STDOUT)
    text=log.read_text(errors="replace")
    rows=[]
    for m in DIAG.finditer(text):
        d=m.groupdict(); d["line"]=int(d["line"]); d["column"]=int(d["column"]); rows.append(d)
    es=[x for x in rows if x["severity"]=="error"]; ws=[x for x in rows if x["severity"]=="warning"]
    r={"variant":variant,"phase":phase,"exit":p.returncode,"error_headers":len(es),"warning_headers":len(ws),
       "panic_lines":len(PANIC.findall(text)),"first_error":es[0] if es else None,"last_error":es[-1] if es else None,
       "error_codes":dict(collections.Counter((x.get("code") or "uncoded") for x in es)),
       "log_sha256":hashlib.sha256(log.read_bytes()).hexdigest(),"candidate_qym_sha256":sha(src),
       "olean_exists":olean.exists() and olean.stat().st_size>0,"ilean_exists":ilean.exists() and ilean.stat().st_size>0}
    dump(OUT/f"{variant}.{phase}.json",r); return r

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    original=OUT/"QYM.original.lean"; shutil.copy2(QYM,original)
    if sha(original)!=BASE_SHA256: raise SystemExit("checked-in branch is not exact V9 GB83 source")
    candidates=[]
    try:
        for v in VARIANTS:
            c=OUT/f"QYM.candidate-{v}.lean"; shutil.copy2(original,c)
            with (OUT/f"{v}.patch.json").open("wb") as h:
                subprocess.run([sys.executable,"-B",str(PATCHER),v,str(c)],check=True,stdout=h)
            local=compile(c,v,"local",8)
            first=(local.get("first_error") or {}).get("line") or 10**9
            local_pass=local["panic_lines"]==0 and first>44197
            candidates.append({"variant":v,"path":str(c),"local":local,"local_pass":local_pass})
        viable=[x for x in candidates if x["local_pass"]]
        viable.sort(key=lambda x: -((x["local"].get("first_error") or {}).get("line") or 10**9))
        full_rows=[]
        for x in viable[:2]:
            full=compile(Path(x["path"]),x["variant"],"full",10000)
            full["baseline_error_headers"]=BASE_ERRORS
            full["semantic_pass"]=full["exit"]==0 and full["error_headers"]==0 and full["panic_lines"]==0 and full["olean_exists"] and full["ilean_exists"]
            full["strict_improvement"]=full["semantic_pass"] or (full["panic_lines"]==0 and full["error_headers"]<BASE_ERRORS)
            full["run_id"]=os.environ.get("GITHUB_RUN_ID"); full["trigger_sha"]=os.environ.get("GITHUB_SHA")
            dump(OUT/f"{x['variant']}.FULL_RESULT.json",full); x["full"]=full; full_rows.append(x)
        improved=[x for x in full_rows if x["full"]["strict_improvement"]]
        sel={"baseline_errors":BASE_ERRORS,"baseline_sha256":BASE_SHA256,"candidates":candidates,"strict_improvement_found":bool(improved)}
        if improved:
            improved.sort(key=lambda x:(x["full"]["error_headers"],-((x["full"].get("first_error") or {}).get("line") or 0)))
            best=improved[0]; sel["best_variant"]=best["variant"]; sel["best"]=best["full"]
            shutil.copy2(Path(best["path"]),OUT/"QYM.best.lean"); dump(OUT/"BEST_RESULT.json",best["full"]); dump(OUT/"SELECTION.json",sel)
            return 0
        dump(OUT/"SELECTION.json",sel); return 2
    finally:
        shutil.copy2(original,QYM)

if __name__=="__main__": raise SystemExit(main())
