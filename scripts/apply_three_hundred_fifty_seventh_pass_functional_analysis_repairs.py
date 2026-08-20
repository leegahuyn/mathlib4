from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "1d707d18ee59aa3fb3e854e8d5425f77daab3258d051d811f733f6199537d1d8"
EXPECTED_OUTPUT_SHA256 = "21a7329098ae02d52b09749d60ba382b3721b65a423094c79d1e16806eabacd1"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrence(s), found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass357] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass357 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(
        text,
        """    _ = 0 := by
      exact
        (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = (0 : ℝ))
""",
        """    _ = 0 := by
      simp
""",
        "FunctionalAnalysis close the zero-form norm by contextual simplification",
    )
    text = replace_exact(
        text,
        """  simp only [smul_apply, smul_eq_mul]
  push_cast
  ring
""",
        """  simp only [smul_apply, smul_eq_mul]
  push_cast
  rw [integral_const_mul]
  ring
""",
        "FunctionalAnalysis pull scalar multiplication through the formal-adjoint integrals",
        expected=2,
    )
    text = replace_exact(
        text,
        """  simp only [← starRingEnd_apply, map_mul, map_pow]
  rw [show (Complex.normSq j : ℂ) = star j * j by
    exact Complex.normSq_eq_conj_mul_self]
""",
        """  have hstarMul :
      star (j ^ (2 : ℕ) * p) = star (j ^ (2 : ℕ)) * star p := by
    simpa only [starRingEnd_apply] using
      (map_mul (starRingEnd ℂ) (j ^ (2 : ℕ)) p)
  have hstarPow :
      star (j ^ (2 : ℕ)) = (star j) ^ (2 : ℕ) := by
    simpa only [starRingEnd_apply] using
      (map_pow (starRingEnd ℂ) j (2 : ℕ))
  rw [hstarMul, hstarPow]
  rw [show (Complex.normSq j : ℂ) = star j * j by
    exact Complex.normSq_eq_conj_mul_self]
""",
        "FunctionalAnalysis expose star multiplication and power explicitly",
    )
    text = replace_exact(
        text,
        """  rw [fixedPhaseIntegralWeightFactor_covariance,
    WeightSection.covariance inverseEtaSection,
    inverseEtaPaperOrbitMultiplier_factor]
  ring_nf
""",
        """  rw [fixedPhaseIntegralWeightFactor_covariance,
    WeightSection.covariance inverseEtaSection,
    inverseEtaPaperOrbitMultiplier_factor]
  change
    inverseEtaPaperOrbitDenom γ z ^ (n * 2) *
          fixedPhaseIntegralWeightFactor n z *
        (inverseEtaMultiplier GammaTwo).factor γ z *
          inverseEtaSection z =
      fixedPhaseIntegralWeightFactor n z * inverseEtaSection z *
        (inverseEtaMultiplier GammaTwo).factor γ z *
          inverseEtaPaperOrbitDenom γ z ^ (2 * n)
  rw [mul_comm n 2]
  ring
""",
        "FunctionalAnalysis normalize the all-index seed covariance",
    )
    text = replace_exact(
        text,
        """      simpa only [Function.mem_support] using hz
""",
        """      simpa only [Function.mem_support, gammaTwoQuotientMk] using hz
""",
        "FunctionalAnalysis unfold the effective quotient representative",
    )
    text = replace_exact(
        text,
        """open DefinitionOneSobolev.FixedPhasePeterssonCoordinates
open scoped LinearPMap

/-! ### Canonical double-adjoint closures on the physical tower -/
""",
        """open DefinitionOneSobolev.FixedPhasePeterssonCoordinates
open scoped LinearPMap

noncomputable local instance fixedPhaseClosedTowerCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact Submodule.module (inverseEtaFixedPhaseStableCoreSubmodule n)

noncomputable local instance fixedPhaseClosedTowerCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  exact Module.addCommMonoidToAddCommGroup ℂ

/-! ### Canonical double-adjoint closures on the physical tower -/
""",
        "FunctionalAnalysis restore coherent closed-tower core instances",
    )
    text = replace_exact(
        text,
        """noncomputable def reindexedActualLower (n : ℤ) :
    InverseEtaFixedPhaseCore (n + 1) →ₗ[ℂ]
      InverseEtaFixedPhaseCore n :=
  InverseEtaFixedPhaseCore.lowerFromSucc n

/-- The transported actual lowering map is exactly the separately typed
`lowerFromSucc`; both have the same raw differential expression and stable-core
proof. -/
theorem reindexedActualLower_eq_lowerFromSucc (n : ℤ) :
    reindexedActualLower n = InverseEtaFixedPhaseCore.lowerFromSucc n :=
  rfl
""",
        """noncomputable def reindexedActualLower (n : ℤ) :
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
""",
        "FunctionalAnalysis restore the literal transported lowering map",
    )
    text = replace_exact(
        text,
        """    _ = 0 := integral_zero
""",
        """    _ = 0 := by simp
""",
        "FunctionalAnalysis close the restricted zero integral",
    )
    text = replace_exact(
        text,
        """  (gammaTwoQuotientCompactFluxTailTightness X Y hFlux)
    .eventually_selectedHorocycle_fluxIntegral_eq_zero
""",
        """  HasZeroThreeCuspTail.eventually_selectedHorocycle_fluxIntegral_eq_zero
    (gammaTwoQuotientCompactFluxTailTightness X Y hFlux)
""",
        "FunctionalAnalysis apply the compact-flux tail theorem explicitly",
    )
    text = replace_exact(
        text,
        """  (fixedPhaseGreenFlux_hasZeroThreeCuspTail n u v)
    .eventually_selectedHorocycle_fluxIntegral_eq_zero
""",
        """  HasZeroThreeCuspTail.eventually_selectedHorocycle_fluxIntegral_eq_zero
    (fixedPhaseGreenFlux_hasZeroThreeCuspTail n u v)
""",
        "FunctionalAnalysis apply the fixed-phase tail theorem explicitly",
    )
    text = replace_exact(
        text,
        """open GammaTwoQuotientGreenBoundary
open scoped LinearPMap

/-! ### The actual raising, lowering, and one-half Green identities -/
""",
        """open GammaTwoQuotientGreenBoundary
open scoped LinearPMap

noncomputable local instance fixedPhaseGreenCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact Submodule.module (inverseEtaFixedPhaseStableCoreSubmodule n)

noncomputable local instance fixedPhaseGreenCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  exact Module.addCommMonoidToAddCommGroup ℂ

/-! ### The actual raising, lowering, and one-half Green identities -/
""",
        "FunctionalAnalysis restore coherent Green-section core instances",
    )
    text = replace_exact(
        text,
        """  simpa only [physicalLowerFromSucc_on_core, physicalRaise_on_core,
    l2CoreRangeEquiv_coe, LinearPMap.neg_apply, inner_neg_right] using hFormal
""",
        """  rw [physicalLowerFromSucc_on_core, LinearPMap.neg_apply,
    physicalRaise_on_core, l2CoreRangeEquiv_coe] at hFormal
  simpa only [inner_neg_right] using hFormal
""",
        "FunctionalAnalysis expose the physical lowering formal-adjoint identity",
    )
    text = replace_exact(
        text,
        """noncomputable def graphLowerFromSuccExtension (n : ℤ) :
    GraphSobolevCompletion (n + 1) →L[ℂ]
      OrbitPeterssonHilbert n := by
  simpa only [add_sub_cancel_right] using
    (lowerExtension (n + 1))
""",
        """noncomputable def graphLowerFromSuccExtension (n : ℤ) :
    GraphSobolevCompletion (n + 1) →L[ℂ]
      OrbitPeterssonHilbert n := by
  have hIndex : n + 1 - 1 = n := by omega
  rw [← hIndex]
  exact lowerExtension (n + 1)
""",
        "FunctionalAnalysis transport the completed lowering target explicitly",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass357 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass357] FunctionalAnalysis algebra, typeclass, tail, and reindex roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
