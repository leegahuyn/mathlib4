from pathlib import Path
import hashlib,json,re,sys
out=Path(sys.argv[1]); p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before=p.read_text()
decl_rx=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0=[m.group('name') for m in decl_rx.finditer(before)]
forbidden=['sorry','admit','axiom','set_option']
fc0={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',before)) for x in forbidden}
after=before

# idx3548: SLAction used by the cusp scaling action is noncomputable.
old='''def gammaTwoLocalCuspCoordinate (κ : GammaTwoCusp) (z : ℍ) : ℂ :=
  (((gammaTwoCuspScaling κ)⁻¹ • z : ℍ) : ℂ)'''
new='''noncomputable def gammaTwoLocalCuspCoordinate (κ : GammaTwoCusp) (z : ℍ) : ℂ :=
  (((gammaTwoCuspScaling κ)⁻¹ • z : ℍ) : ℂ)'''
assert after.count(old)==1,after.count(old); after=after.replace(old,new,1)

# idx3556: expose both qParam occurrences before using integer multiples of the period.
start=after.index('theorem gammaTwoLocalCuspQ_translation'); end=after.index('/-- Every local cusp parameter',start); block=after[start:end]
old='''  rw [gammaTwoLocalCuspQ, gammaTwoLocalCuspCoordinate_translation]
  simpa [Int.cast_mul, mul_comm] using
    ((qParam_two_periodic.int_mul n)
      (gammaTwoLocalCuspCoordinate κ z))'''
new='''  change Function.Periodic.qParam 2
      (gammaTwoLocalCuspCoordinate κ (gammaTwoCuspTranslation κ n • z)) =
    Function.Periodic.qParam 2 (gammaTwoLocalCuspCoordinate κ z)
  rw [gammaTwoLocalCuspCoordinate_translation]
  simpa [Int.cast_mul, mul_comm] using
    ((qParam_two_periodic.int_mul n)
      (gammaTwoLocalCuspCoordinate κ z))'''
assert block.count(old)==1,block.count(old); block=block.replace(old,new,1); after=after[:start]+block+after[end:]

# idx3575: after the integrability iff rewrite, prove each direction explicitly.
start=after.index('theorem rankin_origin_power_integrable_iff'); end=after.index('/-- The endpoint `β = 1`',start); block=after[start:end]
old='''  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hT]
  linarith'''
new='''  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hT]
  constructor <;> intro h <;> linarith'''
assert block.count(old)==1,block.count(old); block=block.replace(old,new,1); after=after[:start]+block+after[end:]

p.write_text(after)
seq1=[m.group('name') for m in decl_rx.finditer(after)]
fc1={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',after)) for x in forbidden}
assert seq0==seq1 and fc0==fc1
# Type/signature portions remain unchanged; only computability marker/proof bodies change.
for marker in ['theorem gammaTwoLocalCuspQ_translation','theorem rankin_origin_power_integrable_iff']:
    a0=before.index(marker); a1=after.index(marker); assert before[a0:before.index(':= by',a0)+5]==after[a1:after.index(':= by',a1)+5]
oldhdr='def gammaTwoLocalCuspCoordinate (κ : GammaTwoCusp) (z : ℍ) : ℂ'
newhdr='noncomputable def gammaTwoLocalCuspCoordinate (κ : GammaTwoCusp) (z : ℍ) : ℂ'
assert oldhdr in before and newhdr in after
b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest(); audit_path=out/'PATCH_AUDIT.json'; audit=json.loads(audit_path.read_text())
audit['candidate_sha256']=sha; audit.setdefault('targets',[]).extend(['gammaTwoLocalCuspCoordinate:noncomputable_marker','gammaTwoLocalCuspQ_translation:explicit_qParam_target','rankin_origin_power_integrable_iff:split_iff'])
audit['cusp_rankin_diagnostic_run_id']=31604949652
audit['rankin_probe_run_id']=31601629317
audit['existing_declaration_relative_order_preserved']=True; audit['semantic_public_proposition_change']=False; audit['forbidden_lexical_counts_preserved']=True
audit_path.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(sha+'\n')
