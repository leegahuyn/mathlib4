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
            """  change
    tensorRestriction (locallyConstantLinearPresheaf E)
        (locallyConstantLinearPresheaf F) hUV (localCoefficient P V z) =
      localCoefficient P U
        (tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV z)
  calc
    tensorRestriction (locallyConstantLinearPresheaf E)
        (locallyConstantLinearPresheaf F) hUV (localCoefficient P V z) =
        tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
            (logRadialCoefficient P V z + potentialCoefficient P V z) := by
      rw [localCoefficient_apply]
    _ = tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
            (logRadialCoefficient P V z) +
        tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
            (potentialCoefficient P V z) := by
      exact (tensorRestriction (locallyConstantLinearPresheaf E)
        (locallyConstantLinearPresheaf F) hUV).map_add _ _
    _ = logRadialCoefficient P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) +
        potentialCoefficient P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) := by
      rw [logRadialCoefficient_restrict, potentialCoefficient_restrict]
    _ = localCoefficient P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) := by
      rw [localCoefficient_apply]
""",
            """  change
    tensorRestriction (locallyConstantLinearPresheaf E)
        (locallyConstantLinearPresheaf F) hUV (localCoefficient P V z) =
      localCoefficient P U
        (tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV z)
  rw [localCoefficient_apply, LinearMap.map_add,
    logRadialCoefficient_restrict, potentialCoefficient_restrict,
    localCoefficient_apply]
""",
            1,
            "Mock2 prove local coefficient naturality without an ambiguous calc chain",
        ),
        (
            """theorem nablaTensorId_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (nablaTensorId P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z) := by
  rw [nablaTensorId_localTrivialization,
    nablaTensorId_localTrivialization]
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (potentialCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      potentialCoefficient P U ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ]
        dlogFrame U
  rw [tensorRestriction_tmul, potentialCoefficient_restrict,
    dlogFrame_restrict]
""",
            """theorem nablaTensorId_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (nablaTensorId P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (potentialCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      potentialCoefficient P U ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ]
        dlogFrame U
  rw [tensorRestriction_tmul, potentialCoefficient_restrict,
    dlogFrame_restrict]
""",
            1,
            "Mock2 expose nabla tensor identity before rewriting",
        ),
        (
            """theorem idTensorDq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (idTensorDq P V z) =
      idTensorDq P U ((aqPresheaf E F).res hUV z) := by
  rw [idTensorDq_localTrivialization, idTensorDq_localTrivialization]
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (logRadialCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      logRadialCoefficient P U ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ]
        dlogFrame U
  rw [tensorRestriction_tmul, logRadialCoefficient_restrict,
    dlogFrame_restrict]
""",
            """theorem idTensorDq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (idTensorDq P V z) =
      idTensorDq P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (logRadialCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      logRadialCoefficient P U ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ]
        dlogFrame U
  rw [tensorRestriction_tmul, logRadialCoefficient_restrict,
    dlogFrame_restrict]
""",
            1,
            "Mock2 expose logarithmic tensor identity before rewriting",
        ),
        (
            """theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  rw [Dq_localTrivialization, Dq_localTrivialization]
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (localCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      localCoefficient P U ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ]
        dlogFrame U
  rw [tensorRestriction_tmul, localCoefficient_restrict, dlogFrame_restrict]
""",
            """theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (localCoefficient P V z ⊗ₜ[ℂ] dlogFrame V) =
      localCoefficient P U ((aqPresheaf E F).res hUV z) ⊗ₜ[ℂ]
        dlogFrame U
  rw [tensorRestriction_tmul, localCoefficient_restrict, dlogFrame_restrict]
""",
            1,
            "Mock2 expose the full derivative before rewriting",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
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
            """  have hbad := h 1 4 (by norm_num) (by norm_num)
  have hsqrt4 : Real.sqrt (((4 : ℕ) : ℝ)) = 2 := by
    calc
      Real.sqrt (((4 : ℕ) : ℝ)) = Real.sqrt ((2 : ℝ) ^ 2) := by norm_num
      _ = |(2 : ℝ)| := Real.sqrt_sq_eq_abs 2
      _ = 2 := abs_of_nonneg (by norm_num)
  rw [hsqrt4] at hbad
  norm_num at hbad
""",
            1,
            "Mock2Advanced compute the casted square root of four exactly",
        ),
        (
            """  have hshell :
      ((fun p : ℝ × ℂ => p.1 • p.2) ''
          (Set.Ioo r R ×ˢ Metric.sphere (0 : ℂ) 1)) =
        openComplexAnnulus r R := by
    rw [Set.image_prod]
    simpa [openComplexAnnulus] using
      (Ioo_smul_sphere_zero
        (E := ℂ) (a := r) (b := R) (r := 1) hr one_pos)
""",
            """  have hshell :
      ((fun p : ℝ × ℂ => p.1 • p.2) ''
          (Set.Ioo r R ×ˢ Metric.sphere (0 : ℂ) 1)) =
        openComplexAnnulus r R := by
    rw [Set.image_prod]
    change
      Set.Ioo r R • Metric.sphere (0 : ℂ) 1 =
        openComplexAnnulus r R
    simpa [openComplexAnnulus] using
      (Ioo_smul_sphere_zero
        (E := ℂ) (a := r) (b := R) (r := 1) hr one_pos)
""",
            1,
            "Mock2Advanced identify the annulus image with set scalar multiplication",
        ),
        (
            """  simpa [exteriorPullback, Function.comp_def] using
    hG.comp hinv hmaps
""",
            """  change AnalyticOn ℂ (fun q : ℂ => G q⁻¹)
    (AnalyticContinuation.openComplexAnnulus r R)
  exact hG.comp hinv hmaps
""",
            1,
            "Mock2Advanced expose exterior pullback as inverse composition",
        ),
        (
            """  have htwo : AnalyticOn ℂ (fun q : ℂ ↦ (2 : ℂ) * Psi q) A :=
    analyticOn_const.mul hPsi
  simpa [dictionaryCore] using htwo.sub hS
""",
            """  have htwo : AnalyticOn ℂ (fun q : ℂ ↦ (2 : ℂ) * Psi q) A :=
    analyticOn_const.mul hPsi
  change AnalyticOn ℂ (fun q : ℂ => 2 * Psi q - S q) A
  exact htwo.sub hS
""",
            1,
            "Mock2Advanced expose the analytic dictionary core pointwise",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  have hcomp := hq'.comp_aemeasurable
    (measurable_quotient_mk''.aemeasurable :
      AEMeasurable gammaTwoQuotientMk
        (hyperbolicMeasure.restrict D.carrier))
  simpa [Function.comp_def] using hcomp
""",
            """  have hcomp := hq'.comp_aemeasurable
    (measurable_quotient_mk''.aemeasurable :
      AEMeasurable gammaTwoQuotientMk
        (hyperbolicMeasure.restrict D.carrier))
  change Integrable
    (pointwiseNormDensity P (SmoothCompactCore.toSection u))
    (hyperbolicMeasure.restrict D.carrier)
  simpa only [Function.comp_def, quotientNormSq_mk] using hcomp
""",
            1,
            "FunctionalAnalysis expose IntegrableOn as a restricted measure integral",
        ),
        (
            """theorem SmoothCompactCore.exists_quotientSupport_subset_truncation
    {P : PaperHalfWeightCertificate} {D : GammaTwoFundamentalDomain}
    (E : GammaTwoTruncationExhaustion D) (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (u.toSection : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' E.truncation Y :=
  E.quotient_exhausts_compacts _ u.quotientCompact
""",
            """theorem SmoothCompactCore.exists_quotientSupport_subset_truncation
    {P : PaperHalfWeightCertificate} {D : GammaTwoFundamentalDomain}
    (E : GammaTwoTruncationExhaustion D) (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' E.truncation Y :=
  E.quotient_exhausts_compacts _ (SmoothCompactCore.quotientCompact u)
""",
            1,
            "FunctionalAnalysis make generic truncation support projections explicit",
        ),
        (
            """theorem SmoothCompactCore.support_orbit_has_truncated_representative
    {P : PaperHalfWeightCertificate} {D : GammaTwoFundamentalDomain}
    (E : GammaTwoTruncationExhaustion D) (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ, u.toSection z ≠ 0 →
      ∃ w : ℍ, w ∈ E.truncation Y ∧
        gammaTwoQuotientMk w = gammaTwoQuotientMk z := by
  obtain ⟨Y, hY, hsub⟩ := u.exists_quotientSupport_subset_truncation E
  refine ⟨Y, hY, fun z hz => ?_⟩
  have hzq : gammaTwoQuotientMk z ∈
      quotientTSupport (u.toSection : ℍ → ℂ) :=
    subset_closure ⟨z, hz, rfl⟩
  rcases hsub hzq with ⟨w, hw, hEq⟩
  exact ⟨w, hw, hEq⟩
""",
            """theorem SmoothCompactCore.support_orbit_has_truncated_representative
    {P : PaperHalfWeightCertificate} {D : GammaTwoFundamentalDomain}
    (E : GammaTwoTruncationExhaustion D) (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ,
      SmoothCompactCore.toSection u z ≠ 0 →
      ∃ w : ℍ, w ∈ E.truncation Y ∧
        gammaTwoQuotientMk w = gammaTwoQuotientMk z := by
  obtain ⟨Y, hY, hsub⟩ :=
    SmoothCompactCore.exists_quotientSupport_subset_truncation E u
  refine ⟨Y, hY, fun z hz => ?_⟩
  have hzq : gammaTwoQuotientMk z ∈
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) :=
    subset_closure ⟨z, hz, rfl⟩
  rcases hsub hzq with ⟨w, hw, hEq⟩
  exact ⟨w, hw, hEq⟩
""",
            1,
            "FunctionalAnalysis make generic truncation orbit projections explicit",
        ),
        (
            """theorem SmoothCompactCore.exists_quotientSupport_subset_topologicalTruncation
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (u.toSection : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' gammaTwoTopologicalTruncation Y :=
  gammaTwoTopologicalTruncation_exhausts_compacts _ u.quotientCompact
""",
            """theorem SmoothCompactCore.exists_quotientSupport_subset_topologicalTruncation
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' gammaTwoTopologicalTruncation Y :=
  gammaTwoTopologicalTruncation_exhausts_compacts _
    (SmoothCompactCore.quotientCompact u)
""",
            1,
            "FunctionalAnalysis make topological truncation support explicit",
        ),
        (
            """theorem SmoothCompactCore.support_orbit_has_topologicalTruncation_representative
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ, u.toSection z ≠ 0 →
      ∃ w : ℍ, w ∈ gammaTwoTopologicalTruncation Y ∧
        gammaTwoQuotientMk w = gammaTwoQuotientMk z := by
  obtain ⟨Y, hY, hsub⟩ :=
    u.exists_quotientSupport_subset_topologicalTruncation
  refine ⟨Y, hY, fun z hz => ?_⟩
  have hzq : gammaTwoQuotientMk z ∈
      quotientTSupport (u.toSection : ℍ → ℂ) :=
    subset_closure ⟨z, hz, rfl⟩
  rcases hsub hzq with ⟨w, hw, hEq⟩
  exact ⟨w, hw, hEq⟩
""",
            """theorem SmoothCompactCore.support_orbit_has_topologicalTruncation_representative
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ,
      SmoothCompactCore.toSection u z ≠ 0 →
      ∃ w : ℍ, w ∈ gammaTwoTopologicalTruncation Y ∧
        gammaTwoQuotientMk w = gammaTwoQuotientMk z := by
  obtain ⟨Y, hY, hsub⟩ :=
    SmoothCompactCore.exists_quotientSupport_subset_topologicalTruncation u
  refine ⟨Y, hY, fun z hz => ?_⟩
  have hzq : gammaTwoQuotientMk z ∈
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) :=
    subset_closure ⟨z, hz, rfl⟩
  rcases hsub hzq with ⟨w, hw, hEq⟩
  exact ⟨w, hw, hEq⟩
""",
            1,
            "FunctionalAnalysis make topological truncation orbit projections explicit",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
