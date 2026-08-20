#!/usr/bin/env python3
from __future__ import annotations
import argparse, json, re
from pathlib import Path

DECL_RE = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')

def decls(text: str):
    ms=list(DECL_RE.finditer(text))
    return [(m.group('name'),m.start(),ms[i+1].start() if i+1<len(ms) else len(text)) for i,m in enumerate(ms)]

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--base-source', required=True)
    ap.add_argument('--library', required=True)
    ap.add_argument('--indices', required=True, help='comma-separated declaration indices')
    ap.add_argument('--out-library', required=True)
    ap.add_argument('--report', required=True)
    a=ap.parse_args()
    text=Path(a.base_source).read_text(); ds=decls(text); lib=json.loads(Path(a.library).read_text()); wanted={int(x) for x in a.indices.split(',') if x.strip()}
    roots=[]; report=[]
    for root in lib.get('repairs',[]):
        idx=int(root['declaration_index'])
        if idx not in wanted: continue
        if idx>=len(ds): raise SystemExit(f'declaration index out of range: {idx}')
        name,start,end=ds[idx]
        if name!=root['declaration_name']: raise SystemExit(f'identity drift idx={idx} got={name} expected={root["declaration_name"]}')
        body=text[start:end]
        rr=root.get('replacements') or ([root] if 'old_fragment' in root else [])
        reps=[]
        for rep in rr:
            old,new=rep['old_fragment'],rep['new_fragment']; oc=body.count(old); nc=body.count(new)
            if oc==1:
                reps.append({'old_fragment':old,'new_fragment':new, **({'id':rep['id']} if 'id' in rep else {})})
                report.append({'idx':idx,'name':name,'id':rep.get('id'),'status':'apply','old_count_in_declaration':oc,'new_count_in_declaration':nc})
            elif oc==0 and nc==1:
                report.append({'idx':idx,'name':name,'id':rep.get('id'),'status':'already-applied','old_count_in_declaration':oc,'new_count_in_declaration':nc})
            else:
                raise SystemExit(f'fragment drift idx={idx} id={rep.get("id")} old_in_decl={oc} new_in_decl={nc}')
        if reps:
            roots.append({'declaration_index':idx,'declaration_name':name,'replacements':reps})
    missing=wanted-{int(r['declaration_index']) for r in lib.get('repairs',[])}
    if missing: raise SystemExit(f'requested indices absent from library: {sorted(missing)}')
    Path(a.out_library).write_text(json.dumps({'schema':'fa-filtered-staged-local-v1','source_library':a.library,'requested_indices':sorted(wanted),'repairs':roots},ensure_ascii=False,indent=2)+'\n')
    Path(a.report).write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')

if __name__=='__main__': main()
