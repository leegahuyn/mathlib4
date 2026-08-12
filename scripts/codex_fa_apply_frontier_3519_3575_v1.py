from pathlib import Path
import hashlib, json, re, sys

out = Path(sys.argv[1])
p = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before = p.read_text()
decl_rx = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0 = [m.group('name') for m in decl_rx.finditer(before)]
forbidden = ['sorry','admit','axiom','set_option']
fc0 = {x: len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])', before)) for x in forbidden}
after = before

# idx3519: bridge Complex.re syntax to the generic RCLike.re theorem explicitly.
start = after.index('theorem weakSchrodinger_embeddedMassShift_coercive')
end = after.index('/-! #### The represented Petersson operator -/', start)
block = after[start:end]
old = '''    rw [← norm_sq_eq_re_inner u,
      ← norm_sq_eq_re_inner (baseExtension n u)]
    ring'''
new = '''    have hu : (inner ℂ u u).re = ‖u‖ ^ 2 := by
      change RCLike.re (inner ℂ u u) = ‖u‖ ^ 2
      exact inner_self_eq_norm_sq (𝕜 := ℂ) u
    have hbase :
        (inner ℂ (baseExtension n u) (baseExtension n u)).re =
          ‖baseExtension n u‖ ^ 2 := by
      change RCLike.re
          (inner ℂ (baseExtension n u) (baseExtension n u)) =
        ‖baseExtension n u‖ ^ 2
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (baseExtension n u)
    rw [hu, hbase]
    ring'''
assert block.count(old) == 1, ('idx3519', block.count(old))
block = block.replace(old, new, 1)
after = after[:start] + block + after[end:]

# idx3546: pin the constant Tendsto so C is not left as a metavariable.
start = after.index('theorem reciprocalFourierTail_tendsto_zero')
end = after.index('theorem twoTorus_isCompactOperator_of_reciprocalTail', start)
block = after[start:end]
old = '''  unfold reciprocalFourierTail
  simpa only [div_eq_mul_inv, one_div, mul_zero] using
    tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N + 1)) Filter.atTop (nhds 0))'''
new = '''  unfold reciprocalFourierTail
  have hconst :
      Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
    hconst.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N + 1)) Filter.atTop (nhds 0))'''
assert block.count(old) == 1, ('idx3546', block.count(old))
block = block.replace(old, new, 1)
after = after[:start] + block + after[end:]

# idx3548 cascade: make the sibling Gamma(2) geometry namespace visible.
ns = 'namespace Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoFundamentalDomain'
start = after.index(ns)
end = after.index('end Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoFundamentalDomain', start)
block = after[start:end]
old = '''open UpperHalfPlane

/-! ### P10.1. Genuine width-two local cusp parameters -/'''
new = '''open UpperHalfPlane
open GammaTwoQuotientGeometry

/-! ### P10.1. Genuine width-two local cusp parameters -/'''
assert block.count(old) == 1, ('idx3548_scope', block.count(old))
block = block.replace(old, new, 1)
after = after[:start] + block + after[end:]

# idx3555: keep the real width cast explicit and normalize the exponent by congruence.
start = after.index('theorem qParam_two_periodic')
end = after.index('/-- The local parameter descends through the complete width-two cusp', start)
block = after[start:end]
old = '''theorem qParam_two_periodic :
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
new = '''theorem qParam_two_periodic :
    Function.Periodic (Function.Periodic.qParam 2) (2 : ℂ) := by
  intro w
  unfold Function.Periodic.qParam
  calc
    Complex.exp
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (w + 2) /
          ((2 : ℝ) : ℂ)) =
      Complex.exp
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * w /
          ((2 : ℝ) : ℂ) +
          2 * (Real.pi : ℂ) * Complex.I) := by
            congr 1
            push_cast
            ring
    _ = Complex.exp
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * w /
          ((2 : ℝ) : ℂ)) := by
          rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
'''
assert block.count(old) == 1, ('idx3555', block.count(old))
block = block.replace(old, new, 1)
after = after[:start] + block + after[end:]

# idx3575: after the integrability iff rewrite, explicitly split the iff.
start = after.index('theorem rankin_origin_power_integrable_iff')
end = after.index('/-- The endpoint `β = 1`', start)
block = after[start:end]
old = '''  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hT]
  linarith'''
new = '''  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hT]
  constructor <;> intro h <;> linarith'''
assert block.count(old) == 1, ('idx3575', block.count(old))
block = block.replace(old, new, 1)
after = after[:start] + block + after[end:]

p.write_text(after)
seq1 = [m.group('name') for m in decl_rx.finditer(after)]
fc1 = {x: len(re.findall(r'(?<![A-Za-z0-9_])'+re.escape(x)+r'(?![A-Za-z0-9_])', after)) for x in forbidden}
assert seq0 == seq1
assert fc0 == fc1
for marker in [
    'theorem weakSchrodinger_embeddedMassShift_coercive',
    'theorem reciprocalFourierTail_tendsto_zero',
    'theorem qParam_two_periodic',
    'theorem rankin_origin_power_integrable_iff']:
    a0=before.index(marker); a1=after.index(marker)
    assert before[a0:before.index(':= by',a0)+5] == after[a1:after.index(':= by',a1)+5]

b = p.read_bytes(); sha = hashlib.sha256(b).hexdigest()
audit_path = out/'PATCH_AUDIT.json'
audit = json.loads(audit_path.read_text())
audit['candidate_sha256'] = sha
audit.setdefault('targets', []).extend([
    'weakSchrodinger_embeddedMassShift_coercive:RCLike_re_bridge',
    'reciprocalFourierTail_tendsto_zero:explicit_const_tendsto',
    'GammaTwoFundamentalDomain:open_GammaTwoQuotientGeometry',
    'qParam_two_periodic:explicit_real_width_cast',
    'rankin_origin_power_integrable_iff:split_iff'])
audit['frontier_3519_3575_repairs'] = 'verified_local_repairs_and_scope_cascade_fix'
audit['idx3519_probe_run_id'] = 31603792260
audit['idx3546_idx3575_probe_run_id'] = 31601629317
audit['idx3555_probe_run_id'] = 31603302027
audit['existing_declaration_relative_order_preserved'] = True
audit['semantic_public_proposition_change'] = False
audit['forbidden_lexical_counts_preserved'] = True
audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True)+'\n')
(out/'candidate.sha256').write_text(sha+'\n')
