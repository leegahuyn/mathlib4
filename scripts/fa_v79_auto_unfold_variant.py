#!/usr/bin/env python3
"""Build proof variants from definitions occurring in a theorem statement."""
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path

BOUNDARY = re.compile(r"(?m)^(?:(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example|axiom)\b|namespace\b|section\b|end\b|open\b|attribute\b|variable\b|include\b|omit\b|noncomputable\s+section\b|local\s+(?:instance|attribute|notation)\b|scoped\b|#(?:check|print|eval|reduce|synth|lint)\b)")
TARGET = re.compile(r"(?m)^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+(?P<name>[A-Za-z0-9_\u0080-\uffff.]+)\b")
DEFINITION = re.compile(r"(?m)^(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev)\s+(?P<name>[A-Za-z0-9_\u0080-\uffff.]+)\b")
MODES = ["simp_defs","simp_only_defs","ext_simp_defs","ext_simp_only_defs","clm_ext_simp_defs","clm_ext_simp_only_defs","unfold_rfl","ext_unfold_rfl","clm_ext_unfold_rfl","dsimp_defs","ext_dsimp_defs","clm_ext_dsimp_defs"]

def h(b:bytes)->str:return hashlib.sha256(b).hexdigest()

def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--theorem',required=True);p.add_argument('--mode',choices=MODES,required=True);p.add_argument('--evidence',type=Path,required=True);a=p.parse_args()
 raw=a.source.read_bytes();text=raw.decode();ms=[m for m in TARGET.finditer(text) if m.group('name')==a.theorem]
 if len(ms)!=1:raise SystemExit(f'target count {len(ms)}')
 m=ms[0];start=m.start();bnd=BOUNDARY.search(text,m.end());end=bnd.start() if bnd else len(text);block=text[start:end];marks=list(re.finditer(r":=\s*by\b",block))
 if len(marks)!=1:raise SystemExit(f'body marker count {len(marks)}')
 mark=marks[0];marker_start=start+mark.start();statement=text[start:marker_start];prefix=statement+':= '
 prior=text[:start];defs=[d.group('name') for d in DEFINITION.finditer(prior)]
 identifiers=set(re.findall(r"(?<![A-Za-z0-9_])([A-Za-z_\u0080-\uffff][A-Za-z0-9_\u0080-\uffff.]*)",statement))
 selected=[]
 for name in defs:
  short=name.rsplit('.',1)[-1]
  if name in identifiers or short in identifiers:
   if name not in selected:selected.append(name)
 # Strongly relevant operator names can occur through notation or namespace qualification.
 for token in sorted(identifiers):
  low=token.lower()
  if any(k in low for k in ['discriminant','weightedhard','graphpotential','hardstage']):
   if token not in selected:selected.append(token)
 if not selected:raise SystemExit('no statement definitions discovered')
 arg=', '.join(selected); bracket='['+arg+']'
 templates={
  'simp_defs':f"by\n  simp {bracket}\n",
  'simp_only_defs':f"by\n  simp only {bracket}\n",
  'ext_simp_defs':f"by\n  ext x\n  simp {bracket}\n",
  'ext_simp_only_defs':f"by\n  ext x\n  simp only {bracket}\n",
  'clm_ext_simp_defs':f"by\n  apply ContinuousLinearMap.ext\n  intro x\n  simp {bracket}\n",
  'clm_ext_simp_only_defs':f"by\n  apply ContinuousLinearMap.ext\n  intro x\n  simp only {bracket}\n",
  'unfold_rfl':f"by\n  unfold {arg}\n  rfl\n",
  'ext_unfold_rfl':f"by\n  ext x\n  unfold {arg}\n  rfl\n",
  'clm_ext_unfold_rfl':f"by\n  apply ContinuousLinearMap.ext\n  intro x\n  unfold {arg}\n  rfl\n",
  'dsimp_defs':f"by\n  dsimp {bracket}\n",
  'ext_dsimp_defs':f"by\n  ext x\n  dsimp {bracket}\n",
  'clm_ext_dsimp_defs':f"by\n  apply ContinuousLinearMap.ext\n  intro x\n  dsimp {bracket}\n",
 }
 newblock=prefix+templates[a.mode]+'\n';candidate_text=text[:start]+newblock+text[end:];candidate=candidate_text.encode();delta={t:candidate_text.count(t)-text.count(t) for t in ['sorry','admit','native_decide','Lean.ofReduceBool']}
 if any(v>0 for v in delta.values()):raise SystemExit(delta)
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(candidate);e={'schema':'fa-v79-auto-unfold-v1','source_sha256':h(raw),'candidate_sha256':h(candidate),'candidate_bytes':len(candidate),'candidate_lines':len(candidate_text.splitlines()),'theorem':a.theorem,'mode':a.mode,'statement_definitions':selected,'statement_sha256':h(statement.encode()),'forbidden_token_delta':delta,'trust_bypass_added':False};a.evidence.parent.mkdir(parents=True,exist_ok=True);a.evidence.write_text(json.dumps(e,indent=2,sort_keys=True)+'\n');print(json.dumps(e,sort_keys=True))
if __name__=='__main__':main()
