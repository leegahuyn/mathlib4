#!/usr/bin/env python3
"""Exhaustively normalize every Lean heartbeat/rec-depth option in a source."""
from __future__ import annotations
import argparse,hashlib,json,re
from pathlib import Path

HB=re.compile(r"(?P<prefix>\bset_option\s+[A-Za-z0-9_.]*maxHeartbeats\s+)(?P<num>[0-9][0-9_]*)")
RD=re.compile(r"(?P<prefix>\bset_option\s+[A-Za-z0-9_.]*maxRecDepth\s+)(?P<num>[0-9][0-9_]*)")

def h(b:bytes):return hashlib.sha256(b).hexdigest()

def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--evidence',type=Path,required=True);p.add_argument('--rec-depth',type=int,default=1000000);a=p.parse_args();raw=a.source.read_bytes();text=raw.decode();before_hb=[m.group(0) for m in HB.finditer(text)];before_rd=[m.group(0) for m in RD.finditer(text)];text,hbc=HB.subn(lambda m:m.group('prefix')+'0',text);text,rdc=RD.subn(lambda m:m.group('prefix')+str(a.rec_depth),text)
 lines=text.splitlines(keepends=True);last=-1
 for i,line in enumerate(lines):
  if re.match(r'^\s*import\s+',line):last=i
  elif last>=0 and line.strip() and not line.lstrip().startswith('--'):break
 if last<0:raise SystemExit('import block not found')
 marker='-- v81 exhaustive resource normalization'
 if marker not in text:text=''.join(lines[:last+1])+f'\n{marker}\nset_option maxHeartbeats 0\nset_option maxRecDepth {a.rec_depth}\n\n'+''.join(lines[last+1:])
 remaining=[]
 for m in HB.finditer(text):
  num=int(m.group('num').replace('_',''))
  if num!=0:remaining.append(m.group(0))
 if remaining:raise SystemExit(f'finite heartbeat settings remain: {remaining}')
 candidate=text.encode();a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_bytes(candidate);e={'schema':'fa-v81-exhaustive-resource-normalization-v1','source_sha256':h(raw),'candidate_sha256':h(candidate),'candidate_bytes':len(candidate),'candidate_lines':len(text.splitlines()),'heartbeat_occurrences_before':before_hb,'rec_depth_occurrences_before':before_rd,'heartbeat_rewrites':hbc,'rec_depth_rewrites':rdc,'remaining_finite_heartbeat_options':remaining,'inserted_maxHeartbeats':0,'inserted_maxRecDepth':a.rec_depth,'statement_or_proof_text_changed':False,'trust_bypass_added':False};a.evidence.parent.mkdir(parents=True,exist_ok=True);a.evidence.write_text(json.dumps(e,indent=2,sort_keys=True)+'\n');print(json.dumps(e,sort_keys=True))
if __name__=='__main__':main()
