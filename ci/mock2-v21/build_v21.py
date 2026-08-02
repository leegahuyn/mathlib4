#!/usr/bin/env python3
import csv, re, collections, hashlib, sys
from pathlib import Path

v18, v19, v20, ledger_gz_b64, out = map(Path, sys.argv[1:6])

def parse(path):
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    stack=[]; starts=[]; occ=collections.Counter()
    for idx,line in enumerate(lines):
        st=line.strip()
        m=re.match(r"namespace\s+([A-Za-z0-9_\.]+)", st)
        if m:
            stack.append(("namespace",m.group(1))); continue
        m=re.match(r"(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_\.]+))?$", st)
        if m:
            stack.append(("section",m.group(1) or "")); continue
        if re.match(r"end(?:\s+[A-Za-z0-9_\.]+)?$", st):
            if stack: stack.pop()
            continue
        st2=re.sub(r"^@\[[^\]]*\]\s*","",st)
        m=re.match(r"(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([^\s(:]+)",st2)
        if m:
            ns=".".join(x[1] for x in stack if x[0]=="namespace" and x[1])
            kind=m.group(1); keykind="def" if kind in ("def","abbrev") else kind
            base=(ns,keykind,m.group(2)); o=occ[base]; occ[base]+=1
            starts.append({"s":idx,"ns":ns,"keykind":keykind,"name":m.group(2),"occ":o,"key":base+(o,)})
    for i,d in enumerate(starts):
        d["e"]=starts[i+1]["s"] if i+1<len(starts) else len(lines)
        d["text"]="".join(lines[d["s"]:d["e"]])
    return lines, starts

P={"v18":parse(v18),"v19":parse(v19),"v20":parse(v20)}
M={k:{d["key"]:d for d in ds} for k,(_,ds) in P.items()}

import base64,gzip,io
ledger_text=gzip.decompress(base64.b64decode(ledger_gz_b64.read_text().strip())).decode()
choices={}
for row in csv.DictReader(io.StringIO(ledger_text),delimiter="\t"):
    key=(row["namespace"],row["kind"],row["name"],int(row["occ"]))
    choices[key]=row["source"]

lines, decls=P["v20"]
parts=[]; pos=0; swapped=0
for d in decls:
    parts.extend(lines[pos:d["s"]])
    ver=choices.get(d["key"],"v20")
    src=M.get(ver,{}).get(d["key"],d)
    parts.append(src["text"])
    swapped += ver!="v20"
    pos=d["e"]
parts.extend(lines[pos:])
out.write_text("".join(parts),encoding="utf-8")
print("swapped",swapped,"sha256",hashlib.sha256(out.read_bytes()).hexdigest())
