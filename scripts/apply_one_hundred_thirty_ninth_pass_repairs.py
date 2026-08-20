from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirty_eighth_pass_repairs as pass138
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
            """def framedOperator {E : ModuleCat ℂ} (T : E →ₗ[ℂ] E)
    (U : TopologicalSpace.Opens X) :
    LocallyConstant U E →ₗ[ℂ]
      TensorProduct ℂ (LocallyConstant U E) (Omega1Section U) :=
  (tensorWithForm (dlogFrame U)).comp (pointwiseOperator T U)
""",
            """def framedOperator {E : ModuleCat ℂ} (T : E →ₗ[ℂ] E)
    (U : TopologicalSpace.Opens X) :
    LocallyConstant U E →ₗ[ℂ]
      TensorSection (locallyConstantLinearPresheaf E)
        (omega1Presheaf (X := X)) U :=
  (tensorWithForm (dlogFrame U)).comp (pointwiseOperator T U)
""",
            1,
            "Mock2 state the framed operator directly in the tensor-presheaf carrier",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  · change volume.restrict (Ioo (-δ) δ) =
      volume.restrict (Ioo (-δ) δ)
    rfl
""",
            """  · rw [smoothVolumeUnitData_spectralMeasure]
    simp
""",
            1,
            "Mock2Advanced rewrite the concrete spectral measure before unit scaling",
        ),
        (
            """  classical
  simpa only [normalization_factor, one_mul, discreteSeries_term] using
    (seriesIdentity.selectedMode_add_mass_le_spectralSide
      (0 : Fin 1) m)
""",
            """  classical
  have h := seriesIdentity.selectedMode_add_mass_le_spectralSide
    (0 : Fin 1) m
  change discreteSeries.term (0 : Fin 1) m +
      massFunctional spectralData m ≤ seriesIdentity.spectralSide m at h
  simpa only [discreteSeries_term] using h
""",
            1,
            "Mock2Advanced expose the concrete series stored in the closed identity",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """theorem realSmooth (u : SmoothCompactWeightCore M) :
    RealSmooth (u.toSection : ℍ → ℂ) :=
  u.2.1

 theorem quotientCompact""".replace("\n theorem", "\ntheorem"),
            """theorem realSmooth (u : SmoothCompactWeightCore M) :
    RealSmooth (toSection u : ℍ → ℂ) :=
  u.2.1

theorem quotientCompact""",
            1,
            "FunctionalAnalysis call the weight-core section projection explicitly",
        ),
        (
            """theorem quotientCompact (u : SmoothCompactWeightCore M) :
    HasQuotientCompactSupport (u.toSection : ℍ → ℂ) :=
  u.2.2
""",
            """theorem quotientCompact (u : SmoothCompactWeightCore M) :
    HasQuotientCompactSupport (toSection u : ℍ → ℂ) :=
  u.2.2
""",
            1,
            "FunctionalAnalysis expose the projected section in compact support",
        ),
        (
            """theorem covariance (u : SmoothCompactWeightCore M)
    (γ : GammaTwo) (z : ℍ) :
    u.toSection (γ • z) = M.factor γ z * u.toSection z :=
  u.toSection.covariance γ z
""",
            """theorem covariance (u : SmoothCompactWeightCore M)
    (γ : GammaTwo) (z : ℍ) :
    toSection u (γ • z) = M.factor γ z * toSection u z :=
  WeightSection.covariance (toSection u) γ z
""",
            1,
            "FunctionalAnalysis prove covariance through the explicit WeightSection",
        ),
        (
            """theorem continuous (u : SmoothCompactWeightCore M) :
    Continuous (u.toSection : ℍ → ℂ) :=
  u.realSmooth.continuous
""",
            """theorem continuous (u : SmoothCompactWeightCore M) :
    Continuous (toSection u : ℍ → ℂ) :=
  (realSmooth u).continuous
""",
            1,
            "FunctionalAnalysis derive continuity from the explicit smoothness theorem",
        ),
        (
            """theorem measurable (u : SmoothCompactWeightCore M) :
    Measurable (u.toSection : ℍ → ℂ) :=
  u.continuous.measurable
""",
            """theorem measurable (u : SmoothCompactWeightCore M) :
    Measurable (toSection u : ℍ → ℂ) :=
  (continuous u).measurable
""",
            1,
            "FunctionalAnalysis derive measurability from the explicit continuity theorem",
        ),
        (
            """theorem zero_apply (z : ℍ) :
    (0 : SmoothCompactWeightCore M).toSection z = 0 :=
  rfl
""",
            """theorem zero_apply (z : ℍ) :
    toSection (0 : SmoothCompactWeightCore M) z = 0 :=
  rfl
""",
            1,
            "FunctionalAnalysis state zero evaluation through the explicit projection",
        ),
        (
            """theorem add_apply (u v : SmoothCompactWeightCore M) (z : ℍ) :
    (u + v).toSection z = u.toSection z + v.toSection z :=
  rfl
""",
            """theorem add_apply (u v : SmoothCompactWeightCore M) (z : ℍ) :
    toSection (u + v) z = toSection u z + toSection v z :=
  rfl
""",
            1,
            "FunctionalAnalysis state addition through the explicit projection",
        ),
        (
            """theorem smul_apply (c : ℂ) (u : SmoothCompactWeightCore M) (z : ℍ) :
    (c • u).toSection z = c * u.toSection z :=
  rfl
""",
            """theorem smul_apply (c : ℂ) (u : SmoothCompactWeightCore M) (z : ℍ) :
    toSection (c • u) z = c * toSection u z :=
  rfl
""",
            1,
            "FunctionalAnalysis state scalar multiplication through the projection",
        ),
        (
            """theorem ext {u v : SmoothCompactWeightCore M}
    (h : ∀ z, u.toSection z = v.toSection z) : u = v := by
""",
            """theorem ext {u v : SmoothCompactWeightCore M}
    (h : ∀ z, toSection u z = toSection v z) : u = v := by
""",
            1,
            "FunctionalAnalysis formulate extensionality using explicit projected sections",
        ),
    ])


def main() -> int:
    pass138.main()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
