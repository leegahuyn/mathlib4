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
  rw [localCoefficient_apply, LinearMap.map_add,
    logRadialCoefficient_restrict, potentialCoefficient_restrict,
    localCoefficient_apply]
""",
            """  calc
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
            1,
            "Mock2 prove local coefficient naturality through explicit linearity",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  constructor
  · exact hselected.symm
  · rw [polarPart, hselected]
    exact eq_sub_of_add_eq hsum
""",
            """  constructor
  · exact hselected.symm
  · rw [polarPart, hselected]
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hsum)
""",
            1,
            "Mock2Advanced orient the polar component through additive cancellation",
        ),
        (
            """theorem not_CitedDampingInequality :
    ¬ CitedDampingInequality := by
  intro h
  have hbad := h 1 4 (by norm_num) (by norm_num)
  norm_num at hbad
""",
            """theorem not_CitedDampingInequality :
    ¬ CitedDampingInequality := by
  intro h
  have hbad := h 1 4 (by norm_num) (by norm_num)
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
  rw [hsqrt4] at hbad
  norm_num at hbad
""",
            1,
            "Mock2Advanced normalize the concrete square root in the damping counterexample",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  have heta := WeightSection.covariance inverseEtaSection γ z
  change
    inverseEtaPaperCertificate.multiplier.factor γ z *
          SmoothCompactCore.toSection u z /
        inverseEtaSection (γ • z) =
      SmoothCompactCore.toSection u z / inverseEtaSection z
  change
    inverseEtaPaperCertificate.multiplier.factor γ z *
          SmoothCompactCore.toSection u z /
        ((inverseEtaSection : ℍ → ℂ) (γ • z)) =
      SmoothCompactCore.toSection u z /
        ((inverseEtaSection : ℍ → ℂ) z)
  rw [heta]
""",
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
            1,
            "FunctionalAnalysis normalize inverse-eta covariance as a function equality",
        ),
        (
            """theorem SmoothCompactCore.exists_relativeQuotientSupport_subset_truncationInterior
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧
      gammaTwoRelativeQuotientPreimage
          (quotientTSupport (u.toSection : ℍ → ℂ)) ⊆
        interior (gammaTwoRelativeTruncation Y) :=
  compact_relativeQuotientPreimage_subset_truncationInterior _
    u.quotientCompact
""",
            """theorem SmoothCompactCore.exists_relativeQuotientSupport_subset_truncationInterior
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧
      gammaTwoRelativeQuotientPreimage
          (quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ)) ⊆
        interior (gammaTwoRelativeTruncation Y) :=
  compact_relativeQuotientPreimage_subset_truncationInterior _
    (SmoothCompactCore.quotientCompact u)
""",
            1,
            "FunctionalAnalysis make relative-support projections explicit",
        ),
        (
            """theorem SmoothCompactCore.exists_quotientSupport_subset_globalCuspTruncation
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (u.toSection : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' gammaTwoGlobalCuspTruncation Y :=
  gammaTwoGlobalCuspTruncation_exhausts_compacts _ u.quotientCompact
""",
            """theorem SmoothCompactCore.exists_quotientSupport_subset_globalCuspTruncation
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' gammaTwoGlobalCuspTruncation Y :=
  gammaTwoGlobalCuspTruncation_exhausts_compacts _
    (SmoothCompactCore.quotientCompact u)
""",
            1,
            "FunctionalAnalysis make global-cusp compact support explicit",
        ),
        (
            """theorem SmoothCompactCore.support_orbit_has_globalCuspTruncation_representative
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ, u.toSection z ≠ 0 →
      ∃ w : ℍ, w ∈ gammaTwoGlobalCuspTruncation Y ∧
        gammaTwoQuotientMk w = gammaTwoQuotientMk z := by
  obtain ⟨Y, hY, hsub⟩ :=
    u.exists_quotientSupport_subset_globalCuspTruncation
  refine ⟨Y, hY, fun z hz ↦ ?_⟩
  have hzq : gammaTwoQuotientMk z ∈
      quotientTSupport (u.toSection : ℍ → ℂ) :=
    subset_closure ⟨z, hz, rfl⟩
  rcases hsub hzq with ⟨w, hw, hEq⟩
  exact ⟨w, hw, hEq⟩
""",
            """theorem SmoothCompactCore.support_orbit_has_globalCuspTruncation_representative
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ,
      SmoothCompactCore.toSection u z ≠ 0 →
      ∃ w : ℍ, w ∈ gammaTwoGlobalCuspTruncation Y ∧
        gammaTwoQuotientMk w = gammaTwoQuotientMk z := by
  obtain ⟨Y, hY, hsub⟩ :=
    SmoothCompactCore.exists_quotientSupport_subset_globalCuspTruncation u
  refine ⟨Y, hY, fun z hz ↦ ?_⟩
  have hzq : gammaTwoQuotientMk z ∈
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) :=
    subset_closure ⟨z, hz, rfl⟩
  rcases hsub hzq with ⟨w, hw, hEq⟩
  exact ⟨w, hw, hEq⟩
""",
            1,
            "FunctionalAnalysis make global-cusp support-orbit projections explicit",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
