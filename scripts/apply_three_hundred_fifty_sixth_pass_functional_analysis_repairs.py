from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "a7e2a057912b21923979d7daf9f9ebaab90e0c1805c76c71b94e6cd15e700e1d"
EXPECTED_OUTPUT_SHA256 = "1d707d18ee59aa3fb3e854e8d5425f77daab3258d051d811f733f6199537d1d8"

text = TARGET.read_text(encoding="utf-8")
input_sha = sha256(text.encode("utf-8")).hexdigest()
print(f"input_sha256={input_sha}")
if input_sha == EXPECTED_OUTPUT_SHA256:
    print("[pass356] already applied")
    raise SystemExit(0)
if input_sha != EXPECTED_INPUT_SHA256:
    raise RuntimeError(
        f"unexpected pass356 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
    )

def repl(old,new,label,count=1):
    global text
    n=text.count(old)
    print(label, n)
    if n!=count:
        raise RuntimeError(f'{label}: expected {count}, got {n}')
    text=text.replace(old,new)

repl('''    _ = 0 := by
      simpa using
        (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = 0)
''','''    _ = 0 := by
      exact
        (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = (0 : ℝ))
''','typed zero form norm')

old_conj='''    rw [dx_conj hf z, dy_conj hf z]
    norm_num
    ring
'''
new_conj='''    have hdx :
        dx (fun w => (starRingEnd ℂ) (f w)) z =
          (starRingEnd ℂ) (dx f z) := by
      simpa only [starRingEnd_apply] using dx_conj hf z
    have hdy :
        dy (fun w => (starRingEnd ℂ) (f w)) z =
          (starRingEnd ℂ) (dy f z) := by
      simpa only [starRingEnd_apply] using dy_conj hf z
    rw [hdx, hdy]
    norm_num
    ring
'''
repl(old_conj,new_conj,'typed conjugate derivatives',2)

repl('''  simp only [smul_apply, smul_eq_mul]
  push_cast
  ring_nf
''','''  simp only [smul_apply, smul_eq_mul]
  push_cast
  ring
''','formal adjoint ring normalization',2)

repl('''    simpa only [l2Coordinate_l2CoreRangeEquiv_symm] using
      h ((l2CoreRangeEquiv n).symm x)
        ((l2CoreRangeEquiv (n + 1)).symm y)
''','''    have hxy :=
      h ((l2CoreRangeEquiv n).symm x)
        ((l2CoreRangeEquiv (n + 1)).symm y)
    rw [l2Coordinate_l2CoreRangeEquiv_symm n x,
      l2Coordinate_l2CoreRangeEquiv_symm (n + 1) y] at hxy
    exact hxy
''','green identity coordinate rewrite')

repl('''  have hpSet :
      p ∈ closure ((physicalRaise n).graph :
        Set (OrbitPeterssonHilbert n ×
          OrbitPeterssonHilbert (n + 1))) := by
    simpa only [Submodule.topologicalClosure_coe] using hp
''','''  have hpSet :
      p ∈ closure ((physicalRaise n).graph :
        Set (OrbitPeterssonHilbert n ×
          OrbitPeterssonHilbert (n + 1))) := by
    change p ∈ closure ((physicalRaise n).graph :
      Set (OrbitPeterssonHilbert n × OrbitPeterssonHilbert (n + 1))) at hp
    exact hp
''','raising closure coercion')

repl('''  have hpSet :
      p ∈ closure ((physicalLowerFromSucc n).graph :
        Set (OrbitPeterssonHilbert (n + 1) ×
          OrbitPeterssonHilbert n)) := by
    simpa only [Submodule.topologicalClosure_coe] using hp
''','''  have hpSet :
      p ∈ closure ((physicalLowerFromSucc n).graph :
        Set (OrbitPeterssonHilbert (n + 1) ×
          OrbitPeterssonHilbert n)) := by
    change p ∈ closure ((physicalLowerFromSucc n).graph :
      Set (OrbitPeterssonHilbert (n + 1) × OrbitPeterssonHilbert n)) at hp
    exact hp
''','lowering closure coercion')

repl('''  have hxSet :
      x ∈ closure ((physicalJointFromSucc n).graph :
        Set (OrbitPeterssonHilbert (n + 1) × PhysicalJointTarget n)) := by
    simpa only [Submodule.topologicalClosure_coe] using hx
''','''  have hxSet :
      x ∈ closure ((physicalJointFromSucc n).graph :
        Set (OrbitPeterssonHilbert (n + 1) × PhysicalJointTarget n)) := by
    change x ∈ closure ((physicalJointFromSucc n).graph :
      Set (OrbitPeterssonHilbert (n + 1) × PhysicalJointTarget n)) at hx
    exact hx
''','joint closure coercion')

repl('''    change
      ((z : OrbitPeterssonHilbert (n + 1)),
        (physicalJointFromSucc n z).fst) ∈
          (physicalRaise (n + 1)).graph
    rw [physicalJointFromSucc_fst]
    exact (physicalRaise (n + 1)).mem_graph z
''','''    change
      ((z : OrbitPeterssonHilbert (n + 1)),
        physicalRaise (n + 1) z) ∈
          (physicalRaise (n + 1)).graph
    exact (physicalRaise (n + 1)).mem_graph z
''','joint raising graph projection')

repl('''    change
      ((z : OrbitPeterssonHilbert (n + 1)),
        (physicalJointFromSucc n z).snd) ∈
          (physicalLowerFromSucc n).graph
    rw [physicalJointFromSucc_snd]
    exact (physicalLowerFromSucc n).mem_graph z
''','''    change
      ((z : OrbitPeterssonHilbert (n + 1)),
        physicalLowerFromSucc n z) ∈
          (physicalLowerFromSucc n).graph
    exact (physicalLowerFromSucc n).mem_graph z
''','joint lowering graph projection')

repl('''  have hRaiseClosure :
      projRaise x ∈ (physicalRaise (n + 1)).graph.topologicalClosure := by
    simpa only [Submodule.topologicalClosure_coe] using hRaiseSet
  have hLowerClosure :
      projLower x ∈ (physicalLowerFromSucc n).graph.topologicalClosure := by
    simpa only [Submodule.topologicalClosure_coe] using hLowerSet
''','''  have hRaiseClosure :
      projRaise x ∈ (physicalRaise (n + 1)).graph.topologicalClosure := by
    change projRaise x ∈ closure ((physicalRaise (n + 1)).graph :
      Set (OrbitPeterssonHilbert (n + 1) ×
        OrbitPeterssonHilbert ((n + 1) + 1)))
    exact hRaiseSet
  have hLowerClosure :
      projLower x ∈ (physicalLowerFromSucc n).graph.topologicalClosure := by
    change projLower x ∈ closure ((physicalLowerFromSucc n).graph :
      Set (OrbitPeterssonHilbert (n + 1) × OrbitPeterssonHilbert n))
    exact hLowerSet
''','joint component closure coercions')

repl('''  rw [map_mul, map_pow]
''','''  simp only [← starRingEnd_apply, map_mul, map_pow]
''','star multiplication and power')

repl('''    _ = j ^ ((2 : ℤ) * (m : ℤ)) := by
      simp only [Int.ofNat_eq_coe, Int.reduceOfNat, Int.mul_ofNat,
        zpow_ofNat]
''','''    _ = j ^ ((2 : ℤ) * (m : ℤ)) := by
      rw [show (2 : ℤ) * (m : ℤ) = ((2 * m : ℕ) : ℤ) by omega]
      exact (zpow_ofNat j (2 * m)).symm
''','positive power integer transport')

repl('''    (j ^ (-2 : ℤ)) ^ (m + 1) =
        (j ^ (-2 : ℤ)) ^ (((m + 1 : ℕ) : ℤ)) := by
      simp only [zpow_ofNat]
''','''    (j ^ (-2 : ℤ)) ^ (m + 1) =
        (j ^ (-2 : ℤ)) ^ (((m + 1 : ℕ) : ℤ)) := by
      exact (zpow_ofNat (j ^ (-2 : ℤ)) (m + 1)).symm
''','negative power nat to int transport')

repl('''    _ = j ^ ((2 : ℤ) * Int.negSucc m) := by
      congr 1
      omega
''','''    _ = j ^ ((2 : ℤ) * Int.negSucc m) := by
      congr 1 <;> omega
''','negative exponent arithmetic')

repl('''      rw [fixedPhasePositiveWeightGenerator_covariance, mul_pow,
        positiveWeightPower_eq_zpow]
''','''      rw [fixedPhasePositiveWeightGenerator_covariance, mul_pow,
        positiveWeightPower_eq_zpow]
      rfl
''','positive factor covariance closure')

repl('''      rw [fixedPhaseNegativeWeightGenerator_covariance, mul_pow,
        negativeWeightPower_eq_zpow]
''','''      rw [fixedPhaseNegativeWeightGenerator_covariance, mul_pow,
        negativeWeightPower_eq_zpow]
      rfl
''','negative factor covariance closure')

repl('''  rw [fixedPhaseIntegralWeightFactor_covariance,
    WeightSection.covariance inverseEtaSection,
    inverseEtaPaperOrbitMultiplier_factor]
  ring
''','''  rw [fixedPhaseIntegralWeightFactor_covariance,
    WeightSection.covariance inverseEtaSection,
    inverseEtaPaperOrbitMultiplier_factor]
  ring_nf
''','seed covariance normalization')

repl('''  · intro hz
    refine ⟨z, ?_, rfl⟩
    simpa only [Function.mem_support,
      quotientAllIndexCoreCutoff_mk] using hz
''','''  · intro hz
    refine ⟨z, ?_, rfl⟩
    have hz' :
        quotientAllIndexCoreCutoff (gammaTwoQuotientMk z) ≠ 0 := by
      simpa only [Function.mem_support] using hz
    change upstairsAllIndexCoreCutoff z ≠ 0
    rw [← quotientAllIndexCoreCutoff_mk]
    exact hz'
''','upstairs cutoff support reverse')

start='''noncomputable def reindexedActualLower (n : ℤ) :
    InverseEtaFixedPhaseCore (n + 1) →ₗ[ℂ]
      InverseEtaFixedPhaseCore n := by
  simpa only [add_sub_cancel_right] using
    (InverseEtaFixedPhaseCore.lower (n + 1))

/-- The transported actual lowering map is exactly the separately typed
`lowerFromSucc`; both have the same raw differential expression and stable-core
proof. -/
theorem reindexedActualLower_eq_lowerFromSucc (n : ℤ) :
    reindexedActualLower n = InverseEtaFixedPhaseCore.lowerFromSucc n := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  rfl
'''
new='''noncomputable def reindexedActualLower (n : ℤ) :
    InverseEtaFixedPhaseCore (n + 1) →ₗ[ℂ]
      InverseEtaFixedPhaseCore n :=
  InverseEtaFixedPhaseCore.lowerFromSucc n

/-- The transported actual lowering map is exactly the separately typed
`lowerFromSucc`; both have the same raw differential expression and stable-core
proof. -/
theorem reindexedActualLower_eq_lowerFromSucc (n : ℤ) :
    reindexedActualLower n = InverseEtaFixedPhaseCore.lowerFromSucc n :=
  rfl
'''
repl(start,new,'canonical successor lowering reindex')

output_sha = sha256(text.encode("utf-8")).hexdigest()
print(f"output_sha256={output_sha}")
if output_sha != EXPECTED_OUTPUT_SHA256:
    raise RuntimeError(
        f"unexpected pass356 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
    )
TARGET.write_text(text, encoding="utf-8")
print("[pass356] FunctionalAnalysis analytic, graph-closure, covariance, and reindex roots repaired")
