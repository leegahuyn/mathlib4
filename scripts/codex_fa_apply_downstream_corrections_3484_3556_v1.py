from pathlib import Path
import hashlib
import json
import re
import sys

out = Path(sys.argv[1])
p = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
before = p.read_text()
decl_rx = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+(?P<name>[^\s(:]+)')
seq0 = [m.group('name') for m in decl_rx.finditer(before)]
forbidden = ['sorry', 'admit', 'axiom', 'set_option']
fc0 = {x: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(x) + r'(?![A-Za-z0-9_])', before)) for x in forbidden}
after = before

# idx3484: the concrete coefficient accepts TwoTorusL2 directly; remove nonexistent alias cast.
old = 'UnitAddTorus.mFourierCoeff (f : TwoTorusFun) k'
new = 'UnitAddTorus.mFourierCoeff f k'
assert after.count(old) == 1, after.count(old)
after = after.replace(old, new, 1)

# idx3492: expose linearity of the inner product in the second argument.
start = after.index('noncomputable def associatedFormGraph')
end = after.index('@[simp]', start)
block = after[start:end]
old = '      simpa [hBu v]'
new = '      simpa [hBu v, inner_smul_right]'
assert block.count(old) == 1, block.count(old)
block = block.replace(old, new, 1)
after = after[:start] + block + after[end:]

# idx3519: norm_sq_eq_re_inner rewrites norm^2 to re(inner), so use forward direction.
start = after.index('theorem weakSchrodinger_embeddedMassShift_coercive')
end = after.index('/-! #### The represented Petersson operator', start)
block = after[start:end]
old = '''    rw [← norm_sq_eq_re_inner u,
      ← norm_sq_eq_re_inner (baseExtension n u)]'''
new = '''    rw [norm_sq_eq_re_inner u,
      norm_sq_eq_re_inner (baseExtension n u)]'''
assert block.count(old) == 1, block.count(old)
block = block.replace(old, new, 1)
after = after[:start] + block + after[end:]

# idx3546: pin the constant sequence so tendsto_const_nhds does not leave a metavariable.
start = after.index('theorem reciprocalFourierTail_tendsto_zero')
end = after.index('theorem twoTorus_isCompactOperator_of_reciprocalTail', start)
block = after[start:end]
old = '''theorem reciprocalFourierTail_tendsto_zero (C : ℝ) :
    Filter.Tendsto (reciprocalFourierTail C) Filter.atTop (nhds 0) := by
  unfold reciprocalFourierTail
  simpa only [div_eq_mul_inv, one_div, mul_zero] using
    tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun N : ℕ ↦ (1 : ℝ) / (N + 1)) Filter.atTop (nhds 0))

'''
new = '''theorem reciprocalFourierTail_tendsto_zero (C : ℝ) :
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
assert block.count(old) == 1, block.count(old)
block = block.replace(old, new, 1)
after = after[:start] + block + after[end:]

# idx3548+: the cusp objects live in the earlier GammaTwoQuotientGeometry namespace.
old = '''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoFundamentalDomain

open UpperHalfPlane
'''
new = '''namespace Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoFundamentalDomain

open UpperHalfPlane
open GammaTwoQuotientGeometry
'''
assert after.count(old) == 1, after.count(old)
after = after.replace(old, new, 1)

# idx3555: make the width-two divisor and translated constant syntactically complex.
start = after.index('theorem qParam_two_periodic')
end = after.index('/-- The local parameter descends', start)
block = after[start:end]
old = '''      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (w + 2) / 2 =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * w / 2 +
          2 * (Real.pi : ℂ) * Complex.I := by'''
new = '''      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (w + (2 : ℂ)) / (2 : ℂ) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I * w / (2 : ℂ) +
          (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by'''
assert block.count(old) == 1, block.count(old)
block = block.replace(old, new, 1)
after = after[:start] + block + after[end:]

p.write_text(after)
seq1 = [m.group('name') for m in decl_rx.finditer(after)]
fc1 = {x: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(x) + r'(?![A-Za-z0-9_])', after)) for x in forbidden}
assert seq0 == seq1
assert fc0 == fc1

# Textual public declaration headers remain byte-identical.
for marker in [
    'theorem twoTorusFiniteFourierProjection_tendsto',
    'noncomputable def associatedFormGraph',
    'theorem weakSchrodinger_embeddedMassShift_coercive',
    'theorem reciprocalFourierTail_tendsto_zero',
    'def gammaTwoLocalCuspCoordinate',
    'theorem qParam_two_periodic']:
    a0 = before.index(marker); a1 = after.index(marker)
    stop0 = before.index(':=', a0) + 2
    stop1 = after.index(':=', a1) + 2
    assert before[a0:stop0] == after[a1:stop1], marker

b = p.read_bytes(); sha = hashlib.sha256(b).hexdigest()
audit_path = out / 'PATCH_AUDIT.json'; audit = json.loads(audit_path.read_text())
audit['candidate_sha256'] = sha
audit.setdefault('targets', []).extend([
    'twoTorusFiniteFourierProjection_tendsto:no_TwoTorusFun_cast',
    'associatedFormGraph:inner_smul_right',
    'weakSchrodinger_embeddedMassShift_coercive:norm_sq_direction',
    'reciprocalFourierTail_tendsto_zero:typed_constant_sequence',
    'GammaTwoFundamentalDomain:open_GammaTwoQuotientGeometry',
    'qParam_two_periodic:explicit_complex_two'])
audit['downstream_corrections_source_diagnostic_run_id'] = 31600803579
audit['existing_declaration_relative_order_preserved'] = True
audit['semantic_public_proposition_change'] = False
audit['forbidden_lexical_counts_preserved'] = True
audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n')
(out / 'candidate.sha256').write_text(sha + '\n')
