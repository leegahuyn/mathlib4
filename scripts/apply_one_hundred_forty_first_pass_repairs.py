from __future__ import annotations

from pathlib import Path

import apply_one_hundred_fortieth_pass_repairs as pass140
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
            """theorem framedOperator_restrict {E : ModuleCat ℂ}
    (T : E →ₗ[ℂ] E) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (s : LocallyConstant V E) :
    tensorRestriction (locallyConstantLinearPresheaf E)
        (omega1Presheaf (X := X)) hUV (framedOperator T V s) =
      framedOperator T U ((locallyConstantLinearPresheaf E).res hUV s) := by
  change
    (locallyConstantRestriction E hUV (pointwiseOperator T V s)) ⊗ₜ[ℂ]
        (locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V)) =
      pointwiseOperator T U (locallyConstantRestriction E hUV s) ⊗ₜ[ℂ]
        dlogFrame U
  have hpoint :
      locallyConstantRestriction E hUV (pointwiseOperator T V s) =
        pointwiseOperator T U (locallyConstantRestriction E hUV s) := by
    apply LocallyConstant.ext
    intro x
    rfl
  have hframe :
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U := by
    apply LocallyConstant.ext
    intro x
    rfl
  rw [hpoint, hframe]
""",
            1,
            "Mock2 prove framed restriction after unfolding categorical carriers",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """theorem selectedMode_add_mass_le_spectralSide (m : ℕ) :
    spectralData.test 0 + massFunctional spectralData m ≤
      seriesIdentity.spectralSide m := by
  classical
  simpa only [normalization_factor, one_mul, discreteSeries_term] using
    (seriesIdentity.selectedMode_add_mass_le_spectralSide
      (0 : Fin 1) m)
""",
            """theorem selectedMode_add_mass_le_spectralSide (m : ℕ) :
    spectralData.test 0 + massFunctional spectralData m ≤
      seriesIdentity.spectralSide m := by
  classical
  have h := seriesIdentity.selectedMode_add_mass_le_spectralSide
    (0 : Fin 1) m
  have hterm :
      seriesIdentity.discreteSeries.term (0 : Fin 1) m =
        spectralData.test 0 := by
    change discreteSeries.term (0 : Fin 1) m = spectralData.test 0
    exact discreteSeries_term m
  rw [hterm] at h
  exact h
""",
            1,
            "Mock2Advanced rewrite the selected closed-series term explicitly",
        ),
        (
            "∑ i in s, energy i",
            "∑ i ∈ s, energy i",
            2,
            "Mock2Advanced update finite energy-sum syntax",
        ),
        (
            "∑ _i in s, L",
            "∑ _i ∈ s, L",
            2,
            "Mock2Advanced update constant finite-sum syntax",
        ),
        (
            "∑ m in blocks k, coefficient m ^ 2",
            "∑ m ∈ blocks k, coefficient m ^ 2",
            5,
            "Mock2Advanced update block mean-square sum syntax",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """theorem inverseEtaRatio_continuous
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Continuous (inverseEtaRatio u) := by
  unfold inverseEtaRatio
  exact u.continuous.div continuous_inverseEtaSection
    inverseEtaSection_apply_ne_zero
""",
            """theorem inverseEtaRatio_continuous
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Continuous (inverseEtaRatio u) := by
  unfold inverseEtaRatio
  exact (SmoothCompactCore.continuous u).div continuous_inverseEtaSection
    inverseEtaSection_apply_ne_zero
""",
            1,
            "FunctionalAnalysis use the explicit core continuity theorem",
        ),
        (
            """theorem inverseEtaRatio_support
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Function.support (inverseEtaRatio u) =
      Function.support (u.toSection : ℍ → ℂ) := by
""",
            """theorem inverseEtaRatio_support
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Function.support (inverseEtaRatio u) =
      Function.support (SmoothCompactCore.toSection u : ℍ → ℂ) := by
""",
            1,
            "FunctionalAnalysis state inverse-eta support via the explicit projection",
        ),
        (
            """  rw [hγ z, WeightSection.covariance u γ z,
    WeightSection.covariance inverseEtaSection γ z]
""",
            """  rw [hγ z, SmoothCompactCore.covariance u γ z,
    WeightSection.covariance inverseEtaSection γ z]
""",
            1,
            "FunctionalAnalysis rewrite core covariance through its namespace theorem",
        ),
        (
            """      gammaTwoQuotientMk ''
        Function.support (u.toSection : ℍ → ℂ) := by
""",
            """      gammaTwoQuotientMk ''
        Function.support (SmoothCompactCore.toSection u : ℍ → ℂ) := by
""",
            1,
            "FunctionalAnalysis state quotient support with explicit projection",
        ),
        (
            """    tsupport (inverseEtaRatioQuotient u) =
      quotientTSupport (u.toSection : ℍ → ℂ) := by
""",
            """    tsupport (inverseEtaRatioQuotient u) =
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) := by
""",
            1,
            "FunctionalAnalysis state quotient topological support explicitly",
        ),
        (
            """  exact u.quotientCompact
""",
            """  exact SmoothCompactCore.quotientCompact u
""",
            1,
            "FunctionalAnalysis use the explicit quotient compactness theorem",
        ),
        (
            """    inverseEtaQuotientScalar u (gammaTwoQuotientMk z) =
      u.toSection z / inverseEtaSection z :=
""",
            """    inverseEtaQuotientScalar u (gammaTwoQuotientMk z) =
      SmoothCompactCore.toSection u z / inverseEtaSection z :=
""",
            1,
            "FunctionalAnalysis expose the projected section in scalar evaluation",
        ),
        (
            """    inverseEtaQuotientLinear u (gammaTwoQuotientMk z) =
      u.toSection z / inverseEtaSection z :=
""",
            """    inverseEtaQuotientLinear u (gammaTwoQuotientMk z) =
      SmoothCompactCore.toSection u z / inverseEtaSection z :=
""",
            1,
            "FunctionalAnalysis expose the projected section in linear evaluation",
        ),
        (
            """  have hz :
      u.toSection z / inverseEtaSection z =
        v.toSection z / inverseEtaSection z := by
""",
            """  have hz :
      SmoothCompactCore.toSection u z / inverseEtaSection z =
        SmoothCompactCore.toSection v z / inverseEtaSection z := by
""",
            1,
            "FunctionalAnalysis formulate injectivity with explicit projected sections",
        ),
    ])


def main() -> int:
    pass140.main()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
