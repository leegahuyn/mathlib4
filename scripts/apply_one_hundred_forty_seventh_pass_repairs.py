from __future__ import annotations

from pathlib import Path

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
            """    rw [TensorProduct.map_tmul, pointwiseOperator_restrict]
  exact LinearMap.congr_fun hmap z

/-- The logarithmic radial coefficient commutes with restriction. -/
""",
            """    rw [TensorProduct.map_tmul]
    have hop := pointwiseOperator_restrict
      (X := X) P.qPotential hUV l
    change
      locallyConstantRestriction E hUV
          (pointwiseOperator P.qPotential V l) =
        pointwiseOperator P.qPotential U
          (locallyConstantRestriction E hUV l) at hop
    rw [hop]
  exact LinearMap.congr_fun hmap z

/-- The logarithmic radial coefficient commutes with restriction. -/
""",
            1,
            "Mock2 transport potential pointwise naturality into the raw tensor carrier",
        ),
        (
            """    rw [TensorProduct.map_tmul, pointwiseOperator_restrict]
  exact LinearMap.congr_fun hmap z

/-- The complete local coefficient `d/d(log r) + A_q(t)` commutes with
""",
            """    rw [TensorProduct.map_tmul]
    have hop := pointwiseOperator_restrict
      (X := X) P.logDerivative hUV m
    change
      locallyConstantRestriction F hUV
          (pointwiseOperator P.logDerivative V m) =
        pointwiseOperator P.logDerivative U
          (locallyConstantRestriction F hUV m) at hop
    rw [hop]
  exact LinearMap.congr_fun hmap z

/-- The complete local coefficient `d/d(log r) + A_q(t)` commutes with
""",
            1,
            "Mock2 transport logarithmic pointwise naturality into the raw tensor carrier",
        ),
        (
            """theorem localCoefficient_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqPresheaf E F).res hUV (localCoefficient P V z) =
      localCoefficient P U ((aqPresheaf E F).res hUV z) := by
  calc
""",
            """theorem localCoefficient_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqPresheaf E F).res hUV (localCoefficient P V z) =
      localCoefficient P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (locallyConstantLinearPresheaf E)
        (locallyConstantLinearPresheaf F) hUV (localCoefficient P V z) =
      localCoefficient P U
        (tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV z)
  calc
""",
            1,
            "Mock2 expose the local coefficient carrier before the calculation",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  have hbad := h 1 4 (by norm_num) (by norm_num)
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
  rw [hsqrt4] at hbad
  norm_num at hbad
""",
            """  have hbad := h 1 4 (by norm_num) (by norm_num)
  have hsqrt4 : Real.sqrt (((4 : ℕ) : ℝ)) = 2 := by
    have hsq := Real.sq_sqrt
      (show (0 : ℝ) ≤ ((4 : ℕ) : ℝ) by norm_num)
    have hnon := Real.sqrt_nonneg (((4 : ℕ) : ℝ))
    norm_num at hsq
    nlinarith
  rw [hsqrt4] at hbad
  norm_num at hbad
""",
            1,
            "Mock2Advanced prove the casted square root of four by squaring",
        ),
        (
            """  have hmul :
      (A * Real.sqrt x) * (2 * r) ≤ r ^ 2 * x + A ^ 2 := by
    rw [← hsqrt_sq]
    nlinarith [sq_nonneg (r * Real.sqrt x - A)]
""",
            """  have hmul :
      (A * Real.sqrt x) * (2 * r) ≤ r ^ 2 * x + A ^ 2 := by
    nlinarith [sq_nonneg (r * Real.sqrt x - A), hsqrt_sq]
""",
            1,
            "Mock2Advanced use the square-root identity as an explicit nonlinear hypothesis",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  have heta := WeightSection.covariance inverseEtaSection γ z
  have heta' :
      (inverseEtaSection : ℍ → ℂ) (γ • z) =
        inverseEtaPaperCertificate.multiplier.factor γ z *
          (inverseEtaSection : ℍ → ℂ) z := by
    simpa using heta
  change
    inverseEtaPaperCertificate.multiplier.factor γ z *
          SmoothCompactCore.toSection u z /
        ((inverseEtaSection : ℍ → ℂ) (γ • z)) =
      SmoothCompactCore.toSection u z /
        ((inverseEtaSection : ℍ → ℂ) z)
  rw [heta']
""",
            """  change
    inverseEtaPaperCertificate.multiplier.factor γ z *
          SmoothCompactCore.toSection u z /
        ((inverseEtaSection : ℍ → ℂ) ((γ : SL(2, ℤ)) • z)) =
      SmoothCompactCore.toSection u z /
        ((inverseEtaSection : ℍ → ℂ) z)
  rw [WeightSection.covariance inverseEtaSection γ z]
""",
            1,
            "FunctionalAnalysis state inverse-eta covariance in the exact integral modular action",
        ),
        (
            """theorem quotientNormSq_support
    (P : PaperHalfWeightCertificate) (u : WeightSection P.multiplier) :
    Function.support (quotientNormSq P u) =
      gammaTwoQuotientMk '' Function.support (u : ℍ → ℂ) := by
  ext q
  induction q using Quotient.inductionOn'
  constructor
  · intro hz
    refine ⟨_, ?_, rfl⟩
    simpa [Function.mem_support, quotientNormSq_mk,
      pointwiseNormDensity_eq_zero_iff] using hz
  · rintro ⟨w, hw, hEq⟩
    have hw' : quotientNormSq P u (gammaTwoQuotientMk w) ≠ 0 := by
      simpa [Function.mem_support, quotientNormSq_mk,
        pointwiseNormDensity_eq_zero_iff] using hw
    rwa [hEq] at hw'
""",
            """theorem quotientNormSq_support
    (P : PaperHalfWeightCertificate) (u : WeightSection P.multiplier) :
    Function.support (quotientNormSq P u) =
      gammaTwoQuotientMk '' Function.support (u : ℍ → ℂ) := by
  ext q
  induction q using Quotient.inductionOn'
  rename_i z
  constructor
  · intro hz
    refine ⟨z, ?_, rfl⟩
    change pointwiseNormDensity P u z ≠ 0 at hz
    exact (pointwiseNormDensity_eq_zero_iff P u z).not.mp hz
  · rintro ⟨w, hw, hEq⟩
    have hw' : quotientNormSq P u (gammaTwoQuotientMk w) ≠ 0 := by
      change pointwiseNormDensity P u w ≠ 0
      exact (pointwiseNormDensity_eq_zero_iff P u w).not.mpr hw
    rwa [hEq] at hw'
""",
            1,
            "FunctionalAnalysis prove quotient norm support through the zero equivalence directly",
        ),
        (
            """theorem SmoothCompactCore.quotientNormSq_hasCompactSupport
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    HasCompactSupport (quotientNormSq P u.toSection) := by
  change IsCompact (tsupport (quotientNormSq P u.toSection))
  rw [quotientNormSq_tsupport]
  exact u.quotientCompact
""",
            """theorem SmoothCompactCore.quotientNormSq_hasCompactSupport
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    HasCompactSupport
      (quotientNormSq P (SmoothCompactCore.toSection u)) := by
  change IsCompact
    (tsupport (quotientNormSq P (SmoothCompactCore.toSection u)))
  rw [quotientNormSq_tsupport]
  exact SmoothCompactCore.quotientCompact u
""",
            1,
            "FunctionalAnalysis make quotient norm compact support projections explicit",
        ),
        (
            """theorem SmoothCompactCore.quotientNormSq_integrable
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P)
    (D : GammaTwoFundamentalDomain) :
    Integrable (quotientNormSq P u.toSection) D.quotientMeasure := by
  exact (quotientNormSq_continuous P u.continuous).integrable_of_hasCompactSupport
    u.quotientNormSq_hasCompactSupport
""",
            """theorem SmoothCompactCore.quotientNormSq_integrable
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P)
    (D : GammaTwoFundamentalDomain) :
    Integrable (quotientNormSq P (SmoothCompactCore.toSection u))
      D.quotientMeasure := by
  exact
    (quotientNormSq_continuous P
      (SmoothCompactCore.continuous u)).integrable_of_hasCompactSupport
        (SmoothCompactCore.quotientNormSq_hasCompactSupport u)
""",
            1,
            "FunctionalAnalysis make quotient norm integrability projections explicit",
        ),
        (
            """theorem SmoothCompactCore.pointwiseNormDensity_integrableOn
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P)
    (D : GammaTwoFundamentalDomain) :
    IntegrableOn (pointwiseNormDensity P u.toSection)
      D.carrier hyperbolicMeasure := by
  have hq := u.quotientNormSq_integrable D
  have hq' : Integrable (quotientNormSq P u.toSection)
      ((hyperbolicMeasure.restrict D.carrier).map gammaTwoQuotientMk) := by
    simpa [GammaTwoFundamentalDomain.quotientMeasure] using hq
""",
            """theorem SmoothCompactCore.pointwiseNormDensity_integrableOn
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P)
    (D : GammaTwoFundamentalDomain) :
    IntegrableOn
      (pointwiseNormDensity P (SmoothCompactCore.toSection u))
      D.carrier hyperbolicMeasure := by
  have hq := SmoothCompactCore.quotientNormSq_integrable u D
  have hq' : Integrable
      (quotientNormSq P (SmoothCompactCore.toSection u))
      ((hyperbolicMeasure.restrict D.carrier).map gammaTwoQuotientMk) := by
    simpa [GammaTwoFundamentalDomain.quotientMeasure] using hq
""",
            1,
            "FunctionalAnalysis make density integrability projections explicit",
        ),
        (
            """theorem SmoothCompactCore.quotientIntegral_eq_fundamentalDomainIntegral
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P)
    (D : GammaTwoFundamentalDomain) :
    ∫ q, quotientNormSq P u.toSection q ∂D.quotientMeasure =
      ∫ z in D.carrier, pointwiseNormDensity P u.toSection z
        ∂hyperbolicMeasure := by
  exact D.integral_quotientMeasure_eq _
    (u.quotientNormSq_integrable D).aestronglyMeasurable
""",
            """theorem SmoothCompactCore.quotientIntegral_eq_fundamentalDomainIntegral
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P)
    (D : GammaTwoFundamentalDomain) :
    ∫ q, quotientNormSq P (SmoothCompactCore.toSection u) q
        ∂D.quotientMeasure =
      ∫ z in D.carrier,
        pointwiseNormDensity P (SmoothCompactCore.toSection u) z
        ∂hyperbolicMeasure := by
  exact D.integral_quotientMeasure_eq _
    (SmoothCompactCore.quotientNormSq_integrable u D).aestronglyMeasurable
""",
            1,
            "FunctionalAnalysis make quotient integral projections explicit",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
