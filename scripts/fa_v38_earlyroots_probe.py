#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys

if len(sys.argv) != 3:
    raise SystemExit('usage: fa_v38_earlyroots_probe.py <v37-source> <outdir>')
source = Path(sys.argv[1])
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
raw = source.read_bytes()
BASE = 'e17ff90193c6959b15f743ef930446b4cfd45bc6df4d762057c13b4b06602d05'
sha = hashlib.sha256(raw).hexdigest()
assert sha == BASE, (sha, BASE)
s = raw.decode('utf-8')

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
new3653 = '''theorem energyForm_eq_inner_strongPrincipalCore
    (n : ℤ) (v u : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore n) :
    (coordinates n).energyForm v u =
      inner ℂ (l2Coordinate n v)
        (l2Coordinate n (strongPrincipalCore n u)) := by
  have hs := successorEnergyForm_eq_inner_strongPrincipalCore (n - 1)
  have hEnergy :
      ∀ (m k : ℤ) (h : k = m) (Q : successorCoordinateType m k)
          (a b : Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore (m + 1)),
        (transportSuccessorCoordinates m k h Q).energyForm a b =
          Q.energyForm a b := by
    intro m k h Q a b
    cases h
    rfl
  simp only [successorGraphCoordinates, hEnergy] at hs
  simpa only [sub_add_cancel] using hs
'''
old3669 = '''    change AEStronglyMeasurable
      (fun p : ℂ × ℂ ↦ v p.1 * K p.2 * u (p.1 - p.2))
      ((volume : Measure ℂ).prod (volume : Measure ℂ))
    simpa only [mul_assoc] using hMeasV.mul hMeasBase
'''
new3669 = '''    change AEStronglyMeasurable
      (fun p : ℂ × ℂ ↦ v p.1 * K p.2 * u (p.1 - p.2))
      ((volume : Measure ℂ).prod (volume : Measure ℂ))
    have hProduct := hMeasV.mul hMeasBase
    change AEStronglyMeasurable
      (fun p : ℂ × ℂ ↦ v p.1 * (K p.2 * u (p.1 - p.2)))
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) at hProduct
    simpa only [mul_assoc] using hProduct
'''
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
  | empty =>
      simpa only [Finset.sum_empty] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ ↦ (0 : ℝ)))
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
for old in (old3653, old3669, old3755):
    assert s.count(old) == 1, old[:120]
s = s.replace(old3653, new3653, 1)
s = s.replace(old3669, new3669, 1)
s = s.replace(old3755, new3755, 1)
full_sha = hashlib.sha256(s.encode()).hexdigest()
# End exactly at a declaration boundary, not an arbitrary source line.
marker = '\ntheorem literalStageCutoffReal_hasCompactSupport'
pos = s.find(marker)
assert pos > 0
prefix = s[:pos] + '\n'
p = out / 'ProbeFA_energy_transport.lean'
p.write_text(prefix)
manifest = {
    'base_sha256': sha,
    'variant': 'energy_transport',
    'full_candidate_sha256': full_sha,
    'prefix_lines': len(prefix.splitlines()),
    'prefix_sha256': hashlib.sha256(prefix.encode()).hexdigest(),
    'repairs': ['3653_energy_transport_invariance','3669_function_product_measurability','3755_finite_partition_contDiff'],
}
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
print(json.dumps(manifest, indent=2, sort_keys=True))
