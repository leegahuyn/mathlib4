#!/usr/bin/env python3
from __future__ import annotations
import hashlib, importlib.util, os, re, sys
from pathlib import Path
ROOT=Path.cwd(); BASE=ROOT/'scripts/fa492_prepare_endpoint_explicit_continuity.py'
spec=importlib.util.spec_from_file_location('fa492base',BASE)
if spec is None or spec.loader is None: raise RuntimeError(f'cannot load {BASE}')
fa492=importlib.util.module_from_spec(spec); sys.modules[spec.name]=fa492; spec.loader.exec_module(fa492)
fa466=fa492.fa466; orig_norm_repairs=fa492.norm_repairs
EXACT_FA492_VARIANT='reuse_hh_endpoint'
RUN='31459011892'; JOB='93678608893'; HEAD='2c7cbbc2ba102674d34e713d18098ed9e7ba30d1'; SRC='91a277662a1cee06b849445865d8a85331a1cef250c150d5c3f5e4c1b66fe7f7'; LINE='35507'; COL='44'; DECL='norm_selectedCuspCoreTrace_sq_le_logHeightEnergy'; IDX='2812'; EXPECTED_LINES=60535
_DECL_START=re.compile(r"(?m)^(?:(?:noncomputable|private|protected|local)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b")
OLD="      unfold selectedLogHeightNaturalGauge; simpa only [h] using ((continuous_const.mul (hh.continuous.comp hpoint)).norm.pow 2)"
NEW="      unfold selectedLogHeightNaturalGauge; simpa only [h, Function.comp_apply] using ((continuous_const.mul (hh.continuous.comp hpoint)).norm.pow 2)"
def sha(s): return hashlib.sha256(s.encode()).hexdigest()
def bounds(text):
 ms=list(_DECL_START.finditer(text)); hs=[i for i,m in enumerate(ms) if m.group('name')==DECL]
 if len(hs)!=1: raise RuntimeError(f'expected one {DECL}, found {len(hs)}')
 i=hs[0]; return ms[i].start(), ms[i+1].start() if i+1<len(ms) else len(text)
def header(r):
 p=r.find(':=');
 if p<0: raise RuntimeError('no :=')
 return r[:p+2]
def req(n,e):
 a=os.environ.get(n)
 if a!=e: raise RuntimeError(f'FA492-r2A requires {n}={e}, got {a!r}')
def norm_repairs(text):
 for n,e in [('FA492_VARIANT',EXACT_FA492_VARIANT),('FA492_EVIDENCE_RUN_ID',RUN),('FA492_EVIDENCE_JOB_ID',JOB),('FA492_EVIDENCE_HEAD_SHA',HEAD),('FA492_EVIDENCE_SOURCE_SHA256',SRC),('FA492_FIRST_ERROR_LINE',LINE),('FA492_FIRST_ERROR_COL',COL),('FA492_FRONTIER_DECLARATION',DECL),('FA492_FRONTIER_INDEX',IDX)]: req(n,e)
 text,reps=orig_norm_repairs(text)
 if sha(text)!=SRC: raise RuntimeError(f'FA492-r2A requires exact FA492 source {SRC}, got {sha(text)}')
 if len(text.splitlines())!=EXPECTED_LINES: raise RuntimeError('line count drift')
 start,end=bounds(text); pre,reg,suf=text[:start],text[start:end],text[end:]; hdr=header(reg)
 if reg.count(OLD)!=1 or reg.count(NEW)!=0: raise RuntimeError(f'target old/new counts {reg.count(OLD)}/{reg.count(NEW)}')
 reg=reg.replace(OLD,NEW,1); cand=pre+reg+suf
 if header(reg)!=hdr or len(cand.splitlines())!=EXPECTED_LINES: raise RuntimeError('invariant drift')
 before=[m.group('name') for m in _DECL_START.finditer(text)]; after=[m.group('name') for m in _DECL_START.finditer(cand)]
 if before!=after: raise RuntimeError('declaration sequence drift')
 audit={'fa492_intermediate_source_sha256':SRC,'candidate_source_sha256':sha(cand),'required_line_count':EXPECTED_LINES,'candidate_line_count':len(cand.splitlines()),'replacement_count':1,'target_header_sha256':sha(hdr),'target_header_preserved':True,'source_prefix_preserved':cand[:start]==pre,'source_suffix_preserved':cand[start+len(reg):]==suf,'declaration_sequence_sha256':sha('\n'.join(before)),'declaration_sequence_preserved':True}
 return cand,reps+[{'declaration':DECL,'declaration_index':int(IDX),'strategy':'normalize the observed continuity function-shape mismatch by adding Function.comp_apply to the final simp-only bridge','matrix_variant':'comp_apply','required_fa492_evidence_run_id':int(RUN),'required_fa492_evidence_job_id':int(JOB),'required_fa492_evidence_head_sha':HEAD,'required_fa492_source_sha256':SRC,'required_fa492_first_error_line':int(LINE),'required_fa492_first_error_col':int(COL),'frontier_declaration_index':int(IDX),'later_repair_count':0,'max_errors':32,**audit},{'declaration':'FA492-r2 sibling A','strategy':'comp_apply','target_declaration':DECL,'target_declaration_index':int(IDX),'later_repair_count':0}]
fa466.norm_repairs=norm_repairs
if __name__=='__main__': fa466.main()
