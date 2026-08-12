from pathlib import Path
import hashlib,json,re,sys
out=Path(sys.argv[1]); p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before=p.read_text()
decl_rx=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0=[m.group('name') for m in decl_rx.finditer(before)]
forbidden=['sorry','admit','axiom','set_option']
fc0={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',before)) for x in forbidden}
after=before

old='UnitAddTorus.mFourierCoeff (f : TwoTorusFun) k'; new='UnitAddTorus.mFourierCoeff f k'
assert after.count(old)==1, after.count(old); after=after.replace(old,new,1)
start=after.index('noncomputable def associatedFormGraph'); end=after.index('@[simp]',start); block=after[start:end]
old='      simpa [hBu v]'; new='      simpa [hBu v, inner_smul_right]'
assert block.count(old)==1,block.count(old); block=block.replace(old,new,1); after=after[:start]+block+after[end:]
p.write_text(after)
seq1=[m.group('name') for m in decl_rx.finditer(after)]
fc1={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',after)) for x in forbidden}
assert seq0==seq1 and fc0==fc1
for marker in ['theorem twoTorusFiniteFourierProjection_tendsto','noncomputable def associatedFormGraph']:
    a0=before.index(marker); a1=after.index(marker); assert before[a0:before.index(':=',a0)+2]==after[a1:after.index(':=',a1)+2]
b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest(); audit_path=out/'PATCH_AUDIT.json'; audit=json.loads(audit_path.read_text())
audit['candidate_sha256']=sha; audit.setdefault('targets',[]).extend(['twoTorusFiniteFourierProjection_tendsto:direct_L2_coeff','associatedFormGraph:inner_smul_right'])
audit['frontier_3484_3492_diagnostic_run_id']=31600803579
audit['associated_graph_scalar_probe_run_id']=31603140641
audit['existing_declaration_relative_order_preserved']=True; audit['semantic_public_proposition_change']=False; audit['forbidden_lexical_counts_preserved']=True
audit_path.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(sha+'\n')
