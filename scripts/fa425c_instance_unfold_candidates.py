#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

THEOREM = "actualEdgeAmbientParam_hasDerivAt"
DECL_RE = re.compile(r"^(?:/--|/-!|theorem\s|lemma\s|def\s|noncomputable\s+def\s|abbrev\s|instance\s|structure\s|namespace\s|section\s|end\b)")


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def locate(lines: list[str]) -> tuple[int, int, int]:
    starts=[i for i,s in enumerate(lines) if s.startswith(f"theorem {THEOREM}")]
    if len(starts)!=1: raise RuntimeError(f"expected one blocker theorem, found {len(starts)}")
    start=starts[0]
    by_line=next(i for i in range(start,start+80) if ":= by" in lines[i])
    end=next(i for i in range(by_line+1,len(lines)) if lines[i] and not lines[i][0].isspace() and DECL_RE.match(lines[i]))
    return start,by_line,end


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--baseline',required=True)
    ap.add_argument('--output',required=True)
    ap.add_argument('--refs',required=False)
    ap.add_argument('--limit',type=int,default=14)
    args=ap.parse_args()

    original=Path(args.baseline).read_text(encoding='utf-8')
    base_lines=original.splitlines(keepends=True)
    count=len(base_lines)
    start,by_line,end=locate(base_lines)
    header=''.join(base_lines[start:by_line+1])
    body=base_lines[by_line+1:end]

    closing_start=None; closing_end=None
    for i,line in enumerate(body):
        if ('simpa' in line or 'exact' in line or 'convert' in line) and closing_start is None:
            # Only consider a closing whose range actually ends in hcomp.
            for j in range(i,min(len(body),i+8)):
                if 'hcomp' in body[j]:
                    closing_start=i; closing_end=j+1; break
        if closing_start is not None: break
    if closing_start is None or closing_end is None:
        # Fallback: select the last nonblank proof line mentioning hcomp.
        hs=[i for i,line in enumerate(body) if 'hcomp' in line]
        if not hs: raise RuntimeError('no hcomp closing found')
        closing_start=hs[-1]; closing_end=hs[-1]+1

    local_indices=[i for i,line in enumerate(body) if 'AddCommGroup Complex' in line and ('letI' in line or 'let ' in line)]
    local_idx=local_indices[0] if local_indices else None

    candidates=[]
    seen=set()
    def add(name:str,new_body:list[str],provenance:str)->None:
        if len(new_body)!=len(body): raise RuntimeError(f'{name}: body height changed')
        out=base_lines[:by_line+1]+new_body+base_lines[end:]
        s=''.join(out)
        out_lines=s.splitlines(keepends=True)
        s0,b0,_=locate(out_lines)
        if len(out_lines)!=count or s0!=start or b0!=by_line: raise RuntimeError(f'{name}: file height/header position changed')
        if ''.join(out_lines[s0:b0+1])!=header: raise RuntimeError(f'{name}: theorem header changed')
        d=sha(s)
        if d in seen:return
        seen.add(d); candidates.append((name,s,provenance,d))

    local_variants={
        'keep': None,
        'canonical': '  letI : AddCommGroup Complex := Complex.instNormedAddCommGroup.toAddCommGroup\n',
        'remove': '  -- canonical Complex additive structure is inferred\n',
    }
    closing_variants={
        'unfold-add': '  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity, Complex.addCommGroup] using hcomp\n',
        'unfold-normed': '  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity, Complex.instNormedAddCommGroup] using hcomp\n',
        'unfold-both': '  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity, Complex.addCommGroup, Complex.instNormedAddCommGroup] using hcomp\n',
        'simp-full-add': '  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity, Complex.addCommGroup] using hcomp\n',
        'simpa-defs': '  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity] using hcomp\n',
        'convert-rfl': '  convert hcomp using 1 <;> rfl\n',
        'exact-hcomp': '  exact hcomp\n',
    }
    width=closing_end-closing_start
    for lname,lreplacement in local_variants.items():
        for cname,closing in closing_variants.items():
            b=list(body)
            if local_idx is not None and lreplacement is not None:
                b[local_idx]=lreplacement
            replacement=[closing]+['\n']*(width-1)
            b[closing_start:closing_end]=replacement
            add(f'{lname}-{cname}',b,f'hand:{lname}+{cname}')

    # Control candidate.
    add('baseline-control',list(body),'verified baseline control')

    out=Path(args.output); out.mkdir(parents=True,exist_ok=True)
    manifest=[]
    for i,(name,text,prov,d) in enumerate(candidates[:args.limit]):
        fn=f'{i:02d}-{name}.lean'; (out/fn).write_text(text,encoding='utf-8')
        manifest.append({'name':name,'provenance':prov,'sha256':d,'file':fn})
    data={
        'theorem':THEOREM,
        'baseline_sha256':sha(original),
        'baseline_line_count':count,
        'theorem_start_line':start+1,
        'theorem_header_sha256':sha(header),
        'closing_start_line':by_line+2+closing_start,
        'closing_height':width,
        'candidate_count':len(manifest),
        'candidates':manifest,
    }
    (out/'MANIFEST.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(data,indent=2))

if __name__=='__main__': main()
