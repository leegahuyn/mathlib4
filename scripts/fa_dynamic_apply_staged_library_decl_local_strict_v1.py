#!/usr/bin/env python3
from __future__ import annotations

import argparse, hashlib, json, re
from pathlib import Path

DECL_RE = re.compile(
    r"(?m)^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"(?P<name>[^\s(:]+)"
)
FORBIDDEN = ("sorry", "admit", "native_decide", "Lean.ofReduceBool", "unsafe")

def sha(b: bytes) -> str: return hashlib.sha256(b).hexdigest()

def decls(text: str) -> list[dict]:
    ms=list(DECL_RE.finditer(text));out=[]
    for i,m in enumerate(ms):
        out.append({'index':i,'name':m.group('name'),'start':m.start(),'end':ms[i+1].start() if i+1<len(ms) else len(text)})
    return out

def header(text: str, d: dict) -> str:
    seg=text[d['start']:d['end']];k=seg.find(':=')
    if k<0: raise RuntimeError(f"declaration {d['index']} {d['name']} has no := terminator")
    return seg[:k+2]

def seq(text: str):
    ns=[d['name'] for d in decls(text)];return ns,sha(('\n'.join(ns)).encode())

def forb(text: str): return {x:text.count(x) for x in FORBIDDEN}

def flatten(lib: dict):
    out=[]
    for root in lib.get('repairs',[]):
        rr=root.get('replacements')
        if rr is None and 'old_fragment' in root and 'new_fragment' in root: rr=[root]
        for r in rr or []:
            out.append({'declaration_index':int(root['declaration_index']),'declaration_name':root['declaration_name'],'staged_header_sha256':root.get('header_sha256'),'old_fragment':r['old_fragment'],'new_fragment':r['new_fragment'],'replacement_id':r.get('id') or root.get('id')})
    for e in lib.get('edits',[]):
        if all(k in e for k in ('declaration_index','declaration_name','old_fragment','new_fragment')):
            out.append({'declaration_index':int(e['declaration_index']),'declaration_name':e['declaration_name'],'staged_header_sha256':e.get('header_sha256'),'old_fragment':e['old_fragment'],'new_fragment':e['new_fragment'],'replacement_id':e.get('id')})
    return out

def main() -> int:
    ap=argparse.ArgumentParser();ap.add_argument('--base-source',required=True);ap.add_argument('--library',required=True);ap.add_argument('--target',required=True);ap.add_argument('--audit-out',required=True);a=ap.parse_args()
    base=Path(a.base_source).read_bytes()
    if b'\r' in base: raise RuntimeError('base source must be LF-only')
    text=base.decode();lib=json.loads(Path(a.library).read_text());names0,seq0=seq(text);forb0=forb(text);applied=[]
    for edit in flatten(lib):
        ds=decls(text);idx=edit['declaration_index']
        if idx>=len(ds): raise RuntimeError(f'repair index out of range: {idx}')
        d=ds[idx]
        if d['name']!=edit['declaration_name']: raise RuntimeError(f"repair declaration identity drift at {idx}: {d['name']} != {edit['declaration_name']}")
        hb=header(text,d);cur_sha=sha(hb.encode());body=text[d['start']:d['end']];old=edit['old_fragment'];new=edit['new_fragment'];oc=body.count(old)
        if oc!=1: raise RuntimeError(f'repair {idx}: old fragment count in declaration={oc}')
        if any(tok in new and tok not in old for tok in FORBIDDEN): raise RuntimeError(f'repair {idx}: forbidden token introduced')
        at=d['start']+body.index(old);text=text[:at]+new+text[at+len(old):]
        da=decls(text)[idx]
        if da['name']!=d['name']: raise RuntimeError(f'repair {idx}: declaration name changed')
        ha=header(text,da)
        if ha!=hb: raise RuntimeError(f'repair {idx}: current theorem proposition/header changed')
        applied.append({'declaration_index':idx,'declaration_name':d['name'],'replacement_id':edit['replacement_id'],'current_header_sha256':cur_sha,'staged_header_sha256':edit['staged_header_sha256'],'staged_header_hash_matches_current_scheme':edit['staged_header_sha256'] in (None,cur_sha),'old_fragment_count_in_declaration':oc,'old_fragment_global_count_observed':text.count(old),'old_fragment_sha256':sha(old.encode()),'new_fragment_sha256':sha(new.encode()),'header_preserved':True})
    if not text.endswith('\n'): text+='\n'
    names1,seq1=seq(text)
    if names1!=names0 or seq1!=seq0: raise RuntimeError('final declaration sequence changed')
    forb1=forb(text)
    if forb1!=forb0: raise RuntimeError(f'forbidden lexical counts changed: {forb0} -> {forb1}')
    p=Path(a.target);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text,encoding='utf-8',newline='\n');data=p.read_bytes()
    mismatches=[{'declaration_index':x['declaration_index'],'declaration_name':x['declaration_name'],'staged_header_sha256':x['staged_header_sha256'],'current_header_sha256':x['current_header_sha256']} for x in applied if x['staged_header_sha256'] is not None and not x['staged_header_hash_matches_current_scheme']]
    audit={'schema':'fa-staged-library-declaration-local-application-audit-v1','library_path':a.library,'library_schema':lib.get('schema'),'base_source_sha256':sha(base),'candidate_source_sha256':sha(data),'candidate_bytes':len(data),'candidate_lines':len(text.splitlines()),'declaration_count':len(names1),'declaration_sequence_sha256':seq1,'declaration_sequence_preserved':True,'public_declaration_headers_preserved':True,'forbidden_counts_before':forb0,'forbidden_counts_after':forb1,'proof_replacements_applied':applied,'declaration_local_uniqueness_enforced':True,'global_old_fragment_uniqueness_required':False,'staged_header_hash_observations':{'mismatches':mismatches,'all_current_headers_preserved':True}}
    Path(a.audit_out).write_text(json.dumps(audit,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
    return 0

if __name__=='__main__': raise SystemExit(main())
