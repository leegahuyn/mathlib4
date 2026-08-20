from pathlib import Path
import hashlib,json,re,sys
out=Path(sys.argv[1]); p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before=p.read_text()
decl_rx=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0=[m.group('name') for m in decl_rx.finditer(before)]
forbidden=['sorry','admit','axiom','set_option']
fc0={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',before)) for x in forbidden}
start=before.index('theorem weakSchrodinger_embeddedMassShift_coercive')
end=before.index('/-! #### The represented Petersson operator',start)
block=before[start:end]
old='''    rw [norm_sq_eq_re_inner u,
      norm_sq_eq_re_inner (baseExtension n u)]
    ring'''
new='''    have huNorm : (inner ℂ u u).re = ‖u‖ ^ 2 := by
      simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
    have hBaseNorm :
        (inner ℂ (baseExtension n u) (baseExtension n u)).re =
          ‖baseExtension n u‖ ^ 2 := by
      simpa using
        (norm_sq_eq_re_inner (𝕜 := ℂ) (baseExtension n u)).symm
    rw [huNorm, hBaseNorm]'''
assert block.count(old)==1,block.count(old)
block=block.replace(old,new,1)
after=before[:start]+block+before[end:]
p.write_text(after)
seq1=[m.group('name') for m in decl_rx.finditer(after)]
fc1={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',after)) for x in forbidden}
assert seq0==seq1 and fc0==fc1
marker='theorem weakSchrodinger_embeddedMassShift_coercive'; a0=before.index(marker); a1=after.index(marker)
assert before[a0:before.index(':= by',a0)+5]==after[a1:after.index(':= by',a1)+5]
b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest(); audit_path=out/'PATCH_AUDIT.json'; audit=json.loads(audit_path.read_text())
audit['candidate_sha256']=sha; audit.setdefault('targets',[]).append('weakSchrodinger_embeddedMassShift_coercive:explicit_complex_inner_norm_v4')
audit['coercive_3519_probe_run_id']=31603892080
audit['coercive_3519_diagnostic_run_id']=31604949652
audit['existing_declaration_relative_order_preserved']=True; audit['semantic_public_proposition_change']=False; audit['forbidden_lexical_counts_preserved']=True
audit_path.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(sha+'\n')
