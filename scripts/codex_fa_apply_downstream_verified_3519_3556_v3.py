from pathlib import Path
import hashlib,json,re,sys
out=Path(sys.argv[1]); p=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before=p.read_text()
decl_rx=re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0=[m.group('name') for m in decl_rx.finditer(before)]
forbidden=['sorry','admit','axiom','set_option']
fc0={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',before)) for x in forbidden}
after=before

# idx3519: bridge Complex.re notation to the generic RCLike theorem explicitly.
start=after.index('theorem weakSchrodinger_embeddedMassShift_coercive'); end=after.index('/-! #### The represented Petersson operator',start); block=after[start:end]
old='''    rw [← norm_sq_eq_re_inner u,
      ← norm_sq_eq_re_inner (baseExtension n u)]
    ring'''
new='''    have huNorm : (inner ℂ u u).re = ‖u‖ ^ 2 := by
      simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
    have hBaseNorm :
        (inner ℂ (baseExtension n u) (baseExtension n u)).re =
          ‖baseExtension n u‖ ^ 2 := by
      simpa using
        (norm_sq_eq_re_inner (𝕜 := ℂ) (baseExtension n u)).symm
    rw [huNorm, hBaseNorm]
    ring'''
assert block.count(old)==1,block.count(old); block=block.replace(old,new,1); after=after[:start]+block+after[end:]

# idx3546: pin both convergent functions before multiplying limits.
start=after.index('theorem reciprocalFourierTail_tendsto_zero'); end=after.index('theorem twoTorus_isCompactOperator_of_reciprocalTail',start); block=after[start:end]
old='''theorem reciprocalFourierTail_tendsto_zero (C : ℝ) :
    Filter.Tendsto (reciprocalFourierTail C) Filter.atTop (nhds 0) := by
  unfold reciprocalFourierTail
  simpa only [div_eq_mul_inv, one_div, mul_zero] using
    tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N + 1)) Filter.atTop (nhds 0))

'''
new='''theorem reciprocalFourierTail_tendsto_zero (C : ℝ) :
    Filter.Tendsto (reciprocalFourierTail C) Filter.atTop (nhds 0) := by
  unfold reciprocalFourierTail
  have hC : Filter.Tendsto (fun _ : ℕ ↦ C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  have hOne : Filter.Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N + 1))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := hC.mul hOne
  simpa [div_eq_mul_inv] using h

'''
assert block.count(old)==1,block.count(old); block=block.replace(old,new,1); after=after[:start]+block+after[end:]

# GammaTwo cusp data were defined in the earlier sibling namespace.
old='''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoFundamentalDomain

open UpperHalfPlane
'''
new='''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoFundamentalDomain

open UpperHalfPlane
open GammaTwoQuotientGeometry
'''
assert after.count(old)==1,after.count(old); after=after.replace(old,new,1)

# idx3555: normalize the qParam target to the same complex numeral representation as harg.
start=after.index('theorem qParam_two_periodic'); end=after.index('/-- The local parameter descends',start); block=after[start:end]
old='''  intro w
  unfold Function.Periodic.qParam
  have harg :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (w + 2) / 2 =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * w / 2 +
          2 * (Real.pi : ℂ) * Complex.I := by
    ring
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]'''
new='''  intro w
  unfold Function.Periodic.qParam
  change Complex.exp
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (w + (2 : ℂ)) / (2 : ℂ)) =
    Complex.exp
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * w / (2 : ℂ))
  have harg :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (w + (2 : ℂ)) / (2 : ℂ) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * w / (2 : ℂ) +
          (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by
    ring
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]'''
assert block.count(old)==1,block.count(old); block=block.replace(old,new,1); after=after[:start]+block+after[end:]

p.write_text(after)
seq1=[m.group('name') for m in decl_rx.finditer(after)]
fc1={x:len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])',after)) for x in forbidden}
assert seq0==seq1 and fc0==fc1
for marker in ['theorem weakSchrodinger_embeddedMassShift_coercive','theorem reciprocalFourierTail_tendsto_zero','def gammaTwoLocalCuspCoordinate','theorem qParam_two_periodic']:
    a0=before.index(marker); a1=after.index(marker); assert before[a0:before.index(':=',a0)+2]==after[a1:after.index(':=',a1)+2]
b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest(); audit_path=out/'PATCH_AUDIT.json'; audit=json.loads(audit_path.read_text())
audit['candidate_sha256']=sha; audit.setdefault('targets',[]).extend(['weakSchrodinger_embeddedMassShift_coercive:explicit_complex_inner_norm','reciprocalFourierTail_tendsto_zero:typed_product_limit','GammaTwoFundamentalDomain:open_GammaTwoQuotientGeometry','qParam_two_periodic:change_complex_width'])
audit['downstream_verified_probe_run_id']=31603892080
audit['gamma_namespace_diagnostic_run_id']=31600803579
audit['existing_declaration_relative_order_preserved']=True; audit['semantic_public_proposition_change']=False; audit['forbidden_lexical_counts_preserved']=True
audit_path.write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n'); (out/'candidate.sha256').write_text(sha+'\n')
