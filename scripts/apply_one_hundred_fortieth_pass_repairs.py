from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirty_ninth_pass_repairs as pass139
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """theorem framedOperator_restrict {E : ModuleCat ℂ}
    (T : E →ₗ[ℂ] E) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (s : LocallyConstant V E) :
    tensorRestriction (locallyConstantLinearPresheaf E)
        (omega1Presheaf (X := X)) hUV (framedOperator T V s) =
      framedOperator T U ((locallyConstantLinearPresheaf E).res hUV s) := by
  rw [framedOperator_apply, tensorRestriction_tmul]
  rw [pointwiseOperator_restrict, dlogFrame_restrict]
  rfl
""",
            """theorem framedOperator_restrict {E : ModuleCat ℂ}
    (T : E →ₗ[ℂ] E) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (s : LocallyConstant V E) :
    tensorRestriction (locallyConstantLinearPresheaf E)
        (omega1Presheaf (X := X)) hUV (framedOperator T V s) =
      framedOperator T U ((locallyConstantLinearPresheaf E).res hUV s) := by
  change
    TensorProduct.map
        ((locallyConstantLinearPresheaf E).restrictionLinear hUV)
        ((omega1Presheaf (X := X)).restrictionLinear hUV)
        ((show (locallyConstantLinearPresheaf E).obj V from
            pointwiseOperator T V s) ⊗ₜ[ℂ]
          (show (omega1Presheaf (X := X)).obj V from dlogFrame V)) =
      (show (locallyConstantLinearPresheaf E).obj U from
          pointwiseOperator T U
            ((locallyConstantLinearPresheaf E).res hUV s)) ⊗ₜ[ℂ]
        (show (omega1Presheaf (X := X)).obj U from dlogFrame U)
  rw [TensorProduct.map_tmul]
  rw [pointwiseOperator_restrict, dlogFrame_restrict]
""",
            1,
            "Mock2 prove framed restriction in the categorical tensor carriers",
        ),
        (
            """def nablaQFactor {E F : ModuleCat ℂ} (P : FibreOperators E F)
    (U : TopologicalSpace.Opens X) :
    LocallyConstant U E →ₗ[ℂ]
      TensorProduct ℂ (LocallyConstant U E) (Omega1Section U) :=
  framedOperator P.qPotential U
""",
            """def nablaQFactor {E F : ModuleCat ℂ} (P : FibreOperators E F)
    (U : TopologicalSpace.Opens X) :
    LocallyConstant U E →ₗ[ℂ]
      TensorSection (locallyConstantLinearPresheaf E)
        (omega1Presheaf (X := X)) U :=
  framedOperator P.qPotential U
""",
            1,
            "Mock2 state the q-factor connection in the tensor-presheaf carrier",
        ),
        (
            """def dQFactor {E F : ModuleCat ℂ} (P : FibreOperators E F)
    (U : TopologicalSpace.Opens X) :
    LocallyConstant U F →ₗ[ℂ]
      TensorProduct ℂ (LocallyConstant U F) (Omega1Section U) :=
  framedOperator P.logDerivative U
""",
            """def dQFactor {E F : ModuleCat ℂ} (P : FibreOperators E F)
    (U : TopologicalSpace.Opens X) :
    LocallyConstant U F →ₗ[ℂ]
      TensorSection (locallyConstantLinearPresheaf F)
        (omega1Presheaf (X := X)) U :=
  framedOperator P.logDerivative U
""",
            1,
            "Mock2 state the logarithmic derivative in the tensor-presheaf carrier",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """theorem selectedMode_add_mass_le_spectralSide (m : ℕ) :
    spectralData.test 0 + massFunctional spectralData m ≤
      seriesIdentity.spectralSide m := by
  classical
  have h := seriesIdentity.selectedMode_add_mass_le_spectralSide
    (0 : Fin 1) m
  change discreteSeries.term (0 : Fin 1) m +
      massFunctional spectralData m ≤ seriesIdentity.spectralSide m at h
  simpa only [discreteSeries_term] using h
""",
            """theorem selectedMode_add_mass_le_spectralSide (m : ℕ) :
    spectralData.test 0 + massFunctional spectralData m ≤
      seriesIdentity.spectralSide m := by
  classical
  simpa only [normalization_factor, one_mul, discreteSeries_term] using
    (seriesIdentity.selectedMode_add_mass_le_spectralSide
      (0 : Fin 1) m)
""",
            1,
            "Mock2Advanced simplify the normalized selected-mode inequality directly",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """theorem realSmooth (u : SmoothCompactCore P) :
    RealSmooth (u.toSection : ℍ → ℂ) :=
  u.2.1

theorem quotientCompact (u : SmoothCompactCore P) :
    HasQuotientCompactSupport (u.toSection : ℍ → ℂ) :=
  u.2.2

theorem covariance (u : SmoothCompactCore P) (γ : GammaTwo) (z : ℍ) :
    u.toSection (γ • z) =
      P.multiplier.factor γ z * u.toSection z :=
  u.toSection.covariance γ z

theorem continuous (u : SmoothCompactCore P) :
    Continuous (u.toSection : ℍ → ℂ) :=
  u.realSmooth.continuous

theorem measurable (u : SmoothCompactCore P) :
    Measurable (u.toSection : ℍ → ℂ) :=
  u.continuous.measurable

@[ext]
theorem ext {u v : SmoothCompactCore P}
    (h : ∀ z, u.toSection z = v.toSection z) : u = v := by
  apply Subtype.ext
  exact WeightSection.ext_apply h

@[simp]
theorem zero_apply (z : ℍ) :
    (0 : SmoothCompactCore P).toSection z = 0 :=
  rfl

@[simp]
theorem add_apply (u v : SmoothCompactCore P) (z : ℍ) :
    (u + v).toSection z = u.toSection z + v.toSection z :=
  rfl

@[simp]
theorem smul_apply (c : ℂ) (u : SmoothCompactCore P) (z : ℍ) :
    (c • u).toSection z = c * u.toSection z :=
  rfl
""",
            """theorem realSmooth (u : SmoothCompactCore P) :
    RealSmooth (toSection u : ℍ → ℂ) :=
  u.2.1

theorem quotientCompact (u : SmoothCompactCore P) :
    HasQuotientCompactSupport (toSection u : ℍ → ℂ) :=
  u.2.2

theorem covariance (u : SmoothCompactCore P) (γ : GammaTwo) (z : ℍ) :
    toSection u (γ • z) =
      P.multiplier.factor γ z * toSection u z :=
  WeightSection.covariance (toSection u) γ z

theorem continuous (u : SmoothCompactCore P) :
    Continuous (toSection u : ℍ → ℂ) :=
  (realSmooth u).continuous

theorem measurable (u : SmoothCompactCore P) :
    Measurable (toSection u : ℍ → ℂ) :=
  (continuous u).measurable

@[ext]
theorem ext {u v : SmoothCompactCore P}
    (h : ∀ z, toSection u z = toSection v z) : u = v := by
  apply Subtype.ext
  exact WeightSection.ext_apply h

@[simp]
theorem zero_apply (z : ℍ) :
    toSection (0 : SmoothCompactCore P) z = 0 :=
  rfl

@[simp]
theorem add_apply (u v : SmoothCompactCore P) (z : ℍ) :
    toSection (u + v) z = toSection u z + toSection v z :=
  rfl

@[simp]
theorem smul_apply (c : ℂ) (u : SmoothCompactCore P) (z : ℍ) :
    toSection (c • u) z = c * toSection u z :=
  rfl
""",
            1,
            "FunctionalAnalysis use explicit projections throughout SmoothCompactCore",
        ),
        (
            """noncomputable def inverseEtaRatio
    (u : SmoothCompactCore inverseEtaPaperCertificate) : ℍ → ℂ :=
  fun z ↦ u.toSection z / inverseEtaSection z
""",
            """noncomputable def inverseEtaRatio
    (u : SmoothCompactCore inverseEtaPaperCertificate) : ℍ → ℂ :=
  fun z ↦ SmoothCompactCore.toSection u z / inverseEtaSection z
""",
            1,
            "FunctionalAnalysis project the inverse-eta core explicitly",
        ),
    ])


def main() -> int:
    pass139.main()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
