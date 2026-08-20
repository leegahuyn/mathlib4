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
replacements = [
    (
        'embeddedMassForm_conj_symm',
        '''  simpa only [embeddedMassForm_apply] using
    (inner_conj_symm (J v) (J u))''',
        '''  change (starRingEnd ℂ) (embeddedMassForm J v u) =
    embeddedMassForm J u v
  simpa only [embeddedMassForm_apply] using
    (inner_conj_symm (J v) (J u))''',
    ),
    (
        'associatedFormGraph',
        '''  smul_mem' := by
    rintro a p ⟨u, hu, hBu⟩
    refine ⟨a • u, by simp only [map_smul, hu, Prod.fst_smul], ?_⟩
    intro v
    simp only [map_smul, ContinuousLinearMap.smul_apply, hBu v,
      Prod.snd_smul, inner_smul_right]''',
        '''  smul_mem' := by
    rintro a p ⟨u, hu, hBu⟩
    refine ⟨a • u, by simp [hu], ?_⟩
    intro v
    simp [hBu v]''',
    ),
    (
        'embeddedShiftedForm_isHermitian',
        '''  intro u v
  simp only [embeddedShiftedForm_apply, map_add, map_mul, map_ofReal,
    inner_conj_symm]
  rw [hB]''',
        '''  intro u v
  rw [embeddedShiftedForm_apply, embeddedShiftedForm_apply]
  change (starRingEnd ℂ)
      (B v u + (c : ℂ) * inner ℂ (J u) (J v)) =
    B u v + (c : ℂ) * inner ℂ (J v) (J u)
  rw [map_add, map_mul, Complex.conj_ofReal, inner_conj_symm]
  change star (B v u) + (c : ℂ) * inner ℂ (J v) (J u) =
    B u v + (c : ℂ) * inner ℂ (J v) (J u)
  rw [hB]''',
    ),
    (
        'associatedFormOperator_realShift_surjective',
        '''  rw [hx, hAx]
  abel''',
        '''  rw [hx, hAx]
  module''',
    ),
    (
        'associatedFormOperator_dense_domain:star_zero',
        '''      _ = star (inner ℂ (J uy) z) := by rw [hSzUy]
      _ = 0 := map_zero (starRingEnd ℂ)''',
        '''      _ = star (inner ℂ (J uy) z) := by rw [hSzUy]
      _ = 0 := by simp [hzy]''',
    ),
    (
        'associatedFormOperator_dense_domain:local_uz',
        '''  have hs := embeddedFormResolventSolution_spec
    J B c α hCoercive z v
  rw [huz, map_zero] at hs
  simpa using hs.symm''',
        '''  have hs := embeddedFormResolventSolution_spec
    J B c α hCoercive z v
  change embeddedShiftedForm J B c uz v = inner ℂ (J v) z at hs
  rw [huz, map_zero] at hs
  simpa using hs.symm''',
    ),
    (
        'weakSchrodingerOperator_isHermitian',
        '''  intro u v
  simp only [weakSchrodingerOperator_apply, map_sub, map_mul,
    map_ofReal, inner_conj_symm]
  rw [graphPotentialOperator_conj_symm]''',
        '''  intro u v
  rw [weakSchrodingerOperator_apply, weakSchrodingerOperator_apply]
  change (starRingEnd ℂ)
      (inner ℂ u v - (t : ℂ) * graphPotentialOperator n v u) =
    inner ℂ v u - (t : ℂ) * graphPotentialOperator n u v
  rw [map_sub, map_mul, Complex.conj_ofReal, inner_conj_symm]
  change inner ℂ v u - (t : ℂ) * star (graphPotentialOperator n v u) =
    inner ℂ v u - (t : ℂ) * graphPotentialOperator n u v
  rw [graphPotentialOperator_conj_symm]''',
    ),
]

for name, old, new in replacements:
    count = after.count(old)
    assert count == 1, (name, count)
    after = after.replace(old, new, 1)

p.write_text(after)
seq1 = [m.group('name') for m in decl_rx.finditer(after)]
fc1 = {x: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(x) + r'(?![A-Za-z0-9_])', after)) for x in forbidden}
assert seq0 == seq1
assert fc0 == fc1

for name in [
    'embeddedMassForm_conj_symm',
    'associatedFormGraph',
    'embeddedShiftedForm_isHermitian',
    'associatedFormOperator_realShift_surjective',
    'associatedFormOperator_dense_domain',
    'weakSchrodingerOperator_isHermitian',
]:
    prefix = 'noncomputable def ' if name == 'associatedFormGraph' else 'theorem '
    marker = prefix + name
    a0 = before.index(marker)
    a1 = after.index(marker)
    assert before[a0:before.index(':=', a0) + 2] == after[a1:after.index(':=', a1) + 2]

b = p.read_bytes()
sha = hashlib.sha256(b).hexdigest()
audit_path = out / 'PATCH_AUDIT.json'
audit = json.loads(audit_path.read_text())
audit['candidate_sha256'] = sha
audit.setdefault('targets', []).extend([
    'embeddedMassForm_conj_symm',
    'associatedFormGraph',
    'embeddedShiftedForm_isHermitian',
    'associatedFormOperator_realShift_surjective',
    'associatedFormOperator_dense_domain',
    'weakSchrodingerOperator_isHermitian',
])
audit['form_downstream_repair'] = 'explicit_starRingEnd_broad_simp_module_and_local_let_normalization'
audit['form_downstream_probe_run_id'] = 31594753234
audit['existing_declaration_relative_order_preserved'] = True
audit['semantic_public_proposition_change'] = False
audit['forbidden_lexical_counts_preserved'] = True
audit_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n')
(out / 'candidate.sha256').write_text(sha + '\n')
