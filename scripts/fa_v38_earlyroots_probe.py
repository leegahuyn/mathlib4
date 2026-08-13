#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

if len(sys.argv) != 3:
    raise SystemExit('usage: fa_v38_earlyroots_probe.py <v37-source> <outdir>')
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
base_bytes = source.read_bytes()
base_sha = hashlib.sha256(base_bytes).hexdigest()
BASE = 'e17ff90193c6959b15f743ef930446b4cfd45bc6df4d762057c13b4b06602d05'
assert base_sha == BASE, (base_sha, BASE)
original = base_bytes.decode('utf-8')

old3653 = '''theorem energyForm_eq_inner_strongPrincipalCore
    (n : ℤ) (v u : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n) :
    (coordinates n).energyForm v u =
      inner ℂ (l2Coordinate n v)
        (l2Coordinate n (strongPrincipalCore n u)) := by
  have hs :=
    successorEnergyForm_eq_inner_strongPrincipalCore (n - 1)
  simpa only [successorGraphCoordinates, transportSuccessorCoordinates,
    successorIndexEq, sub_add_cancel] using hs
'''
head3653 = '''theorem energyForm_eq_inner_strongPrincipalCore
    (n : ℤ) (v u : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n) :
    (coordinates n).energyForm v u =
      inner ℂ (l2Coordinate n v)
        (l2Coordinate n (strongPrincipalCore n u)) := by
'''
core = 'Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore'
variants = {
    'rw_hidx': head3653 + '''  have hs := successorEnergyForm_eq_inner_strongPrincipalCore (n - 1)
  have hidx : n - 1 + 1 = n := sub_add_cancel n 1
  rw [hidx] at hs
  simpa only [successorGraphCoordinates, transportSuccessorCoordinates,
    successorIndexEq, sub_add_cancel] using hs v u
''',
    'simp_hidx': head3653 + '''  have hs := successorEnergyForm_eq_inner_strongPrincipalCore (n - 1)
  have hidx : n - 1 + 1 = n := sub_add_cancel n 1
  simp only [hidx] at hs
  simpa only [successorGraphCoordinates, transportSuccessorCoordinates,
    successorIndexEq, sub_add_cancel] using hs v u
''',
    'cast_convert': head3653 + f'''  have hidx : n - 1 + 1 = n := sub_add_cancel n 1
  let v' : {core} (n - 1 + 1) :=
    Eq.mpr (congrArg {core} hidx) v
  let u' : {core} (n - 1 + 1) :=
    Eq.mpr (congrArg {core} hidx) u
  have hs := successorEnergyForm_eq_inner_strongPrincipalCore (n - 1) v' u'
  convert hs using 1 <;>
    simp [v', u', hidx, successorGraphCoordinates,
      transportSuccessorCoordinates, successorIndexEq]
''',
    'coord_eq_first': head3653 + '''  have hs := successorEnergyForm_eq_inner_strongPrincipalCore (n - 1)
  have hcoord :
      successorGraphCoordinates (n - 1) = coordinates (n - 1 + 1) := by
    simp only [successorGraphCoordinates, transportSuccessorCoordinates,
      successorIndexEq, sub_add_cancel]
  rw [hcoord] at hs
  simpa only [sub_add_cancel] using hs
''',
    'coord_eq_n': head3653 + '''  have hs := successorEnergyForm_eq_inner_strongPrincipalCore (n - 1)
  have hcoord : successorGraphCoordinates (n - 1) = coordinates n := by
    simp only [successorGraphCoordinates, transportSuccessorCoordinates,
      successorIndexEq, sub_add_cancel]
  rw [hcoord] at hs
  simpa only [sub_add_cancel] using hs
''',
}

old3669 = '    simpa only [mul_assoc] using hMeasV.mul hMeasBase'
new3669 = '    simpa only [Pi.mul_apply] using hMeasV.mul hMeasBase'
old3689 = '''        simpa only [map_add, map_smul, neg_smul, one_smul, map_neg,
          sub_eq_add_neg, c] using h.symm)'''
new3689 = '''        simpa only [map_add, map_smul, neg_smul, one_smul, map_neg,
          sub_eq_add_neg, pow_two, c] using h.symm)'''
old3755 = '''theorem literalStageCutoffReal_contDiff (Y : ℝ) :
    ContDiff ℝ ∞ (literalStageCutoffReal Y) := by
  classical
  unfold literalStageCutoffReal
  fun_prop
'''
new3755 = '''theorem literalStageCutoffReal_contDiff (Y : ℝ) :
    ContDiff ℝ ∞ (literalStageCutoffReal Y) := by
  classical
  unfold literalStageCutoffReal
  induction literalStageActiveCenters Y using Finset.induction_on with
  | empty => exact contDiff_const
  | @insert z t hz ih =>
      have hzSmooth : ContDiff ℝ ∞ (literalStagePartition Y z : ℂ → ℝ) := by
        have hp := (literalStagePartition Y z).property
        rw [contMDiff_iff_contDiff] at hp
        have hfun :
            (↑(literalStagePartition Y z) : ℂ → ℝ) =
              (literalStagePartition Y z : ℂ → ℝ) := by
          funext x
          rfl
        rw [← hfun]
        exact hp
      simp only [Finset.sum_insert hz]
      change ContDiff ℝ ∞
        ((literalStagePartition Y z : ℂ → ℝ) +
          (fun w ↦ ∑ x ∈ t, literalStagePartition Y x w))
      exact hzSmooth.add ih
'''
for old in [old3653, old3669, old3689, old3755]:
    assert old in original, old[:120]

manifest = {'base_sha256': base_sha, 'variants': {}}
for name, body in variants.items():
    s = original.replace(old3653, body, 1)
    s = s.replace(old3669, new3669, 1)
    s = s.replace(old3689, new3689, 1)
    s = s.replace(old3755, new3755, 1)
    candidate_sha = hashlib.sha256(s.encode()).hexdigest()
    prefix = ''.join(s.splitlines(True)[:50705])
    p = out / f'ProbeFA_{name}.lean'
    p.write_text(prefix)
    manifest['variants'][name] = {
        'full_candidate_sha256': candidate_sha,
        'prefix_lines': len(prefix.splitlines()),
        'prefix_sha256': hashlib.sha256(prefix.encode()).hexdigest(),
    }
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
print(json.dumps(manifest, indent=2, sort_keys=True))
