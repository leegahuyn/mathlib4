from pathlib import Path
import hashlib
import json
import re
import sys

out = Path(sys.argv[1])
p = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before = p.read_text()
decl_rx = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0=[m.group('name') for m in decl_rx.finditer(before)]
forbidden=['sorry','admit','axiom','set_option']
fc0={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',before)) for x in forbidden}
after=before

# idx3492: make conjugate-linear/right-scalar law explicit.
old='''    · intro v
      simpa [hBu v]'''
new='''    · intro v
      simpa [hBu v, inner_smul_right]'''
# Restrict replacement to associatedFormGraph block.
s=after.index('noncomputable def associatedFormGraph')
e=after.index('@[simp]',s)
block=after[s:e]
assert block.count(old)==1, block.count(old)
block=block.replace(old,new,1)
after=after[:s]+block+after[e:]

# idx3519: avoid metavariable-sensitive rewriting of norm_sq_eq_re_inner.
s=after.index('theorem weakSchrodinger_embeddedMassShift_coercive')
e=after.index('/-! #### The represented Petersson operator',s)
block=after[s:e]
old='''    rw [← norm_sq_eq_re_inner u,
      ← norm_sq_eq_re_inner (baseExtension n u)]
    ring'''
new='''    have hu : (inner ℂ u u).re = ‖u‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
    have hbase :
        (inner ℂ (baseExtension n u) (baseExtension n u)).re =
          ‖baseExtension n u‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) (baseExtension n u)).symm
    rw [hu, hbase]
    ring'''
assert block.count(old)==1, block.count(old)
block=block.replace(old,new,1)
after=after[:s]+block+after[e:]

# idx3548-3560: the cusp data live in the sibling GammaTwoQuotientGeometry namespace.
old='''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoFundamentalDomain

open UpperHalfPlane'''
new='''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoFundamentalDomain

open UpperHalfPlane
open GammaTwoQuotientGeometry'''
assert after.count(old)==1, after.count(old)
after=after.replace(old,new,1)

# idx3555: make the coerced width-two denominator explicit before rewriting.
s=after.index('theorem qParam_two_periodic')
e=after.index('/-- The local parameter descends',s)
block=after[s:e]
old='''theorem qParam_two_periodic :
    Function.Periodic (Function.Periodic.qParam 2) (2 : ℂ) := by
  intro w
  unfold Function.Periodic.qParam
  have harg :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (w + 2) / 2 =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * w / 2 +
          2 * (Real.pi : ℂ) * Complex.I := by
    ring
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
'''
new='''theorem qParam_two_periodic :
    Function.Periodic (Function.Periodic.qParam 2) (2 : ℂ) := by
  intro w
  unfold Function.Periodic.qParam
  change Complex.exp
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (w + 2) / (2 : ℂ)) =
    Complex.exp
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * w / (2 : ℂ))
  have harg :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (w + 2) / (2 : ℂ) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * w / (2 : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I := by
    ring
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
'''
assert block.count(old)==1, block.count(old)
block=block.replace(old,new,1)
after=after[:s]+block+after[e:]

p.write_text(after)
seq1=[m.group('name') for m in decl_rx.finditer(after)]
fc1={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',after)) for x in forbidden}
assert seq0==seq1 and fc0==fc1
for name in ['weakSchrodinger_embeddedMassShift_coercive','qParam_two_periodic']:
    marker='theorem '+name; a0=before.index(marker); a1=after.index(marker)
    assert before[a0:before.index(':= by',a0)+5] == after[a1:after.index(':= by',a1)+5]
# associatedFormGraph is a def; its public header stays byte-identical.
marker='noncomputable def associatedFormGraph'; a0=before.index(marker); a1=after.index(marker)
assert before[a0:before.index(':=',a0)+2] == after[a1:after.index(':=',a1)+2]

b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest()
audit_path=out/'PATCH_AUDIT.json'; audit=json.loads(audit_path.read_text())
audit['candidate_sha256']=sha
audit.setdefault('targets',[]).extend([
  'associatedFormGraph:inner_smul_right',
  'weakSchrodinger_embeddedMassShift_coercive:explicit_norm_sq_equalities',
  'GammaTwoFundamentalDomain:open_GammaTwoQuotientGeometry',
  'qParam_two_periodic:explicit_complex_denominator'])
audit['v10_mid_repair']='inner_smul_norm_sq_namespace_and_qparam_normalization'
audit['v10_mid_probe_run_id']=31603997020
audit['v10_diagnostic_run_id']=31602395683
audit['existing_declaration_relative_order_preserved']=True
audit['semantic_public_proposition_change']=False
audit['forbidden_lexical_counts_preserved']=True
audit_path.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
(out/'candidate.sha256').write_text(sha+'\n')
