from __future__ import annotations

from pathlib import Path

import apply_one_hundred_forty_third_pass_repairs as pass143
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
            """        dlogFrame U := by
  simp only [nablaTensorId, LinearMap.comp_apply, TensorProduct.map_tmul,
    nablaQFactor_apply, leftTensorReassociate_tmul]
""",
            """        dlogFrame U := by
  change
    leftTensorReassociate
        (ModuleCat.of ℂ (LocallyConstant U E))
        (ModuleCat.of ℂ (LocallyConstant U F))
        (ModuleCat.of ℂ (Omega1Section U))
      ((nablaQFactor P U l) ⊗ₜ[ℂ] m) = _
  rw [nablaQFactor_apply, leftTensorReassociate_tmul]
""",
            1,
            "Mock2 expose the left-reassociated pure tensor",
        ),
        (
            """        dlogFrame U := by
  simp only [idTensorDq, LinearMap.comp_apply, TensorProduct.map_tmul,
    dQFactor_apply, rightTensorReassociate_tmul]
""",
            """        dlogFrame U := by
  change
    rightTensorReassociate
        (ModuleCat.of ℂ (LocallyConstant U E))
        (ModuleCat.of ℂ (LocallyConstant U F))
        (ModuleCat.of ℂ (Omega1Section U))
      (l ⊗ₜ[ℂ] dQFactor P U m) = _
  rw [dQFactor_apply, rightTensorReassociate_tmul]
""",
            1,
            "Mock2 expose the right-reassociated pure tensor",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """    _ ≤ testValue * coefficient m ^ 2 + ε :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left (hcoefficient m hm) htestValue) ε
""",
            """    _ ≤ testValue * coefficient m ^ 2 + ε := by
      simpa only [add_comm] using
        (add_le_add_right
          (mul_le_mul_of_nonneg_left (hcoefficient m hm) htestValue) ε)
""",
            1,
            "Mock2Advanced normalize right-added coefficient inequality",
        ),
        (
            """  change P.toLinearMap (φ - P.toLinearMap φ) = 0
  rw [map_sub, LinearMap.congr_fun P.idempotent φ]
  abel_nf
""",
            """  change P.toLinearMap (φ - P.toLinearMap φ) = 0
  rw [map_sub]
  have hidem := LinearMap.congr_fun P.idempotent φ
  change P.toLinearMap (P.toLinearMap φ) = P.toLinearMap φ at hidem
  rw [hidem, sub_self]
""",
            1,
            "Mock2Advanced apply projection idempotence at the evaluated point",
        ),
        (
            """  · rw [polarPart, ← hsum, ← hselected]
    abel
""",
            """  · rw [polarPart, hselected]
    exact eq_sub_of_add_eq hsum
""",
            1,
            "Mock2Advanced derive the unique polar component from the sum equation",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  rw [heta]
  exact mul_div_mul_left _ _
    (inverseEtaPaperCertificate.multiplier.factor_ne_zero γ z)
""",
            """  change
    inverseEtaPaperCertificate.multiplier.factor γ z *
          SmoothCompactCore.toSection u z /
        ((inverseEtaSection : ℍ → ℂ) (γ • z)) =
      SmoothCompactCore.toSection u z /
        ((inverseEtaSection : ℍ → ℂ) z)
  rw [heta]
  exact mul_div_mul_left _ _
    (inverseEtaPaperCertificate.multiplier.factor_ne_zero γ z)
""",
            1,
            "FunctionalAnalysis align inverse-eta function coercions before covariance rewrite",
        ),
        (
            """theorem SmoothCompactCore.exists_quotientSupport_subset_compactStage
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ n : ℕ, quotientTSupport (u.toSection : ℍ → ℂ) ⊆
      gammaTwoQuotientCompactExhaustion n :=
  u.quotientCompact.exists_compactExhaustion_stage
""",
            """theorem SmoothCompactCore.exists_quotientSupport_subset_compactStage
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ n : ℕ,
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) ⊆
        gammaTwoQuotientCompactExhaustion n :=
  HasQuotientCompactSupport.exists_compactExhaustion_stage
    (SmoothCompactCore.quotientCompact u)
""",
            1,
            "FunctionalAnalysis call compact-stage capture through explicit core projections",
        ),
        (
            """theorem SmoothCompactCore.exists_quotientSupport_subset_interior_compactStage
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ n : ℕ, quotientTSupport (u.toSection : ℍ → ℂ) ⊆
      interior (gammaTwoQuotientCompactExhaustion n) :=
  u.quotientCompact.exists_interior_compactExhaustion_stage
""",
            """theorem SmoothCompactCore.exists_quotientSupport_subset_interior_compactStage
    {P : PaperHalfWeightCertificate} (u : SmoothCompactCore P) :
    ∃ n : ℕ,
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) ⊆
        interior (gammaTwoQuotientCompactExhaustion n) :=
  HasQuotientCompactSupport.exists_interior_compactExhaustion_stage
    (SmoothCompactCore.quotientCompact u)
""",
            1,
            "FunctionalAnalysis call interior-stage capture explicitly",
        ),
        (
            """    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (u.toSection : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' gammaTwoThreeCuspTruncation Y :=
  hCofinal _ u.quotientCompact
""",
            """    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' gammaTwoThreeCuspTruncation Y :=
  hCofinal _ (SmoothCompactCore.quotientCompact u)
""",
            1,
            "FunctionalAnalysis expose the core projection in cusp cofinality",
        ),
        (
            """    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ, u.toSection z ≠ 0 →
      ∃ w : ℍ, w ∈ gammaTwoThreeCuspTruncation Y ∧
        gammaTwoQuotientMk w = gammaTwoQuotientMk z := by
  obtain ⟨Y, hY, hsub⟩ :=
    u.exists_quotientSupport_subset_threeCuspTruncation_of_compactCofinal
      hCofinal
  refine ⟨Y, hY, fun z hz ↦ ?_⟩
  have hzq : gammaTwoQuotientMk z ∈
      quotientTSupport (u.toSection : ℍ → ℂ) :=
    subset_closure ⟨z, hz, rfl⟩
""",
            """    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ,
      SmoothCompactCore.toSection u z ≠ 0 →
        ∃ w : ℍ, w ∈ gammaTwoThreeCuspTruncation Y ∧
          gammaTwoQuotientMk w = gammaTwoQuotientMk z := by
  obtain ⟨Y, hY, hsub⟩ :=
    SmoothCompactCore.exists_quotientSupport_subset_threeCuspTruncation_of_compactCofinal
      hCofinal u
  refine ⟨Y, hY, fun z hz ↦ ?_⟩
  have hzq : gammaTwoQuotientMk z ∈
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) :=
    subset_closure ⟨z, hz, rfl⟩
""",
            1,
            "FunctionalAnalysis make the pointwise cusp-capture theorem explicit",
        ),
        (
            """    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (u.toSection : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' gammaTwoThreeCuspTruncation Y :=
  u.exists_quotientSupport_subset_threeCuspTruncation_of_compactCofinal
    gammaTwoThreeCuspCompactCofinal_unconditional
""",
            """    ∃ Y : ℝ, 1 < Y ∧
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) ⊆
        gammaTwoQuotientMk '' gammaTwoThreeCuspTruncation Y :=
  SmoothCompactCore.exists_quotientSupport_subset_threeCuspTruncation_of_compactCofinal
    gammaTwoThreeCuspCompactCofinal_unconditional u
""",
            1,
            "FunctionalAnalysis instantiate unconditional cusp cofinality explicitly",
        ),
        (
            """    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ, u.toSection z ≠ 0 →
      ∃ w : ℍ, w ∈ gammaTwoThreeCuspTruncation Y ∧
        gammaTwoQuotientMk w = gammaTwoQuotientMk z :=
  u.support_orbit_has_threeCuspTruncation_representative_of_compactCofinal
    gammaTwoThreeCuspCompactCofinal_unconditional
""",
            """    ∃ Y : ℝ, 1 < Y ∧ ∀ z : ℍ,
      SmoothCompactCore.toSection u z ≠ 0 →
        ∃ w : ℍ, w ∈ gammaTwoThreeCuspTruncation Y ∧
          gammaTwoQuotientMk w = gammaTwoQuotientMk z :=
  SmoothCompactCore.support_orbit_has_threeCuspTruncation_representative_of_compactCofinal
    gammaTwoThreeCuspCompactCofinal_unconditional u
""",
            1,
            "FunctionalAnalysis instantiate unconditional orbit capture explicitly",
        ),
    ])


def main() -> int:
    pass143.main()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
