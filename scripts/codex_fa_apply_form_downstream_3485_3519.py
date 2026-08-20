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

repls = []
repls.append((
'3485_remove_closed_ring',
'''      have hShiftX :
          inner ℂ ((c : ℂ) • (z : H) + A z) (x : H) =
            inner ℂ (z : H) ((c : ℂ) • (x : H) + A x) := by
        rw [inner_add_left, inner_smul_left, hSymmetricPair,
          inner_add_right, inner_smul_right, Complex.conj_ofReal]
        ring
      have hdd : inner ℂ d d = 0 := by''',
'''      have hShiftX :
          inner ℂ ((c : ℂ) • (z : H) + A z) (x : H) =
            inner ℂ (z : H) ((c : ℂ) • (x : H) + A x) := by
        rw [inner_add_left, inner_smul_left, hSymmetricPair,
          inner_add_right, inner_smul_right, Complex.conj_ofReal]
      have hdd : inner ℂ d d = 0 := by'''))

repls.append((
'3491_mass_conj_starRingEnd',
'''  simpa only [embeddedMassForm_apply] using
    (inner_conj_symm (J v) (J u))''',
'''  change (starRingEnd ℂ) (embeddedMassForm J v u) = embeddedMassForm J u v
  simpa only [embeddedMassForm_apply] using
    (inner_conj_symm (J v) (J u))'''))

repls.append((
'3492_graph_smul_default_simp',
'''  smul_mem' := by
    rintro a p ⟨u, hu, hBu⟩
    refine ⟨a • u, by simp only [map_smul, hu, Prod.fst_smul], ?_⟩
    intro v
    simp only [map_smul, ContinuousLinearMap.smul_apply, hBu v,
      Prod.snd_smul, inner_smul_right]''',
'''  smul_mem' := by
    rintro a p ⟨u, hu, hBu⟩
    refine ⟨a • u, ?_, ?_⟩
    · simpa [hu]
    · intro v
      simpa [hBu v]'''))

repls.append((
'3501_embedded_shift_starRingEnd',
'''  intro u v
  simp only [embeddedShiftedForm_apply, map_add, map_mul, map_ofReal,
    inner_conj_symm]
  rw [hB]''',
'''  intro u v
  change (starRingEnd ℂ) (embeddedShiftedForm J B c v u) =
    embeddedShiftedForm J B c u v
  rw [embeddedShiftedForm_apply, embeddedShiftedForm_apply,
    map_add, map_mul, Complex.conj_ofReal, inner_conj_symm]
  change star (B v u) + (c : ℂ) * inner ℂ (J v) (J u) =
    B u v + (c : ℂ) * inner ℂ (J v) (J u)
  rw [hB]'''))

repls.append((
'3507_real_shift_module',
'''  rw [hx, hAx]
  abel''',
'''  rw [hx, hAx]
  module'''))

repls.append((
'3509_dense_star_zero',
'''      _ = star (inner ℂ (J uy) z) := by rw [hSzUy]
      _ = 0 := map_zero (starRingEnd ℂ)''',
'''      _ = star (inner ℂ (J uy) z) := by rw [hSzUy]
      _ = 0 := by simp [hzy]'''))

repls.append((
'3509_dense_fold_resolvent',
'''  have hs := embeddedFormResolventSolution_spec
    J B c α hCoercive z v
  rw [huz, map_zero] at hs
  simpa using hs.symm''',
'''  have hs := embeddedFormResolventSolution_spec
    J B c α hCoercive z v
  change embeddedShiftedForm J B c uz v = inner ℂ (J v) z at hs
  rw [huz, map_zero] at hs
  simpa using hs.symm'''))

repls.append((
'3514_weak_schrodinger_starRingEnd',
'''  intro u v
  simp only [weakSchrodingerOperator_apply, map_sub, map_mul,
    map_ofReal, inner_conj_symm]
  rw [graphPotentialOperator_conj_symm]''',
'''  intro u v
  change (starRingEnd ℂ) (weakSchrodingerOperator n t v u) =
    weakSchrodingerOperator n t u v
  rw [weakSchrodingerOperator_apply, weakSchrodingerOperator_apply,
    map_sub, map_mul, Complex.conj_ofReal, inner_conj_symm]
  change inner ℂ v u - (t : ℂ) * star (graphPotentialOperator n v u) =
    inner ℂ v u - (t : ℂ) * graphPotentialOperator n u v
  rw [graphPotentialOperator_conj_symm]'''))

repls.append((
'3519_norm_sq_real_inner',
'''    simp only [embeddedShiftedForm_apply,
      weakSchrodingerOperator_apply, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      inner_self_eq_norm_sq, zero_mul, sub_zero]
    ring''',
'''    simp only [embeddedShiftedForm_apply,
      weakSchrodingerOperator_apply, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [← norm_sq_eq_re_inner u,
      ← norm_sq_eq_re_inner (baseExtension n u)]
    ring'''))

for name, old, new in repls:
    c = after.count(old)
    assert c == 1, (name, c)
    after = after.replace(old, new, 1)

p.write_text(after)
seq1 = [m.group('name') for m in decl_rx.finditer(after)]
fc1 = {x: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(x) + r'(?![A-Za-z0-9_])', after)) for x in forbidden}
assert seq0 == seq1
assert fc0 == fc1

for name in [
    'LinearPMap.isSelfAdjoint_of_realShift_surjective',
    'embeddedMassForm_conj_symm',
    'embeddedShiftedForm_isHermitian',
    'associatedFormOperator_realShift_surjective',
    'associatedFormOperator_dense_domain',
    'weakSchrodingerOperator_isHermitian',
    'weakSchrodinger_embeddedMassShift_coercive']:
    marker = 'theorem ' + name
    a0 = before.index(marker)
    a1 = after.index(marker)
    assert before[a0:before.index(':= by', a0) + 5] == after[a1:after.index(':= by', a1) + 5]

b = p.read_bytes()
sha = hashlib.sha256(b).hexdigest()
audit_path = out / 'PATCH_AUDIT.json'
audit = json.loads(audit_path.read_text())
audit['candidate_sha256'] = sha
audit.setdefault('targets', []).extend([x[0] for x in repls])
audit['form_downstream_repair'] = 'starRingEnd_graph_smul_module_dense_and_norm_bridges'
audit['form_downstream_probe_run_id'] = 31594753234
audit['form_downstream_diagnostic_run_id'] = 31594384354
audit['norm_sq_source'] = 'InnerProductSpace.norm_sq_eq_re_inner'
audit['existing_declaration_relative_order_preserved'] = True
audit['semantic_public_proposition_change'] = False
audit['forbidden_lexical_counts_preserved'] = True
audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n')
(out / 'candidate.sha256').write_text(sha + '\n')
