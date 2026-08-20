from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  residual_not_mem_theorem := by decide
""",
            """  residual_not_mem_theorem := by
    simp
""",
            "Mock1Advanced prove residual table separation by simplification",
        ),
        (
            """  rademacher_link := by
    intro n
    rfl
""",
            """  rademacher_link := by
    intro n
    exact referenceNormalizedArchRademacher.coeff_eq n
""",
            "Mock1Advanced reuse the normalized Rademacher coefficient theorem",
        ),
        (
            """  scalar_formula := by norm_num
""",
            """  scalar_formula := referenceArchimedeanScalarRecord.scalar_eq
""",
            "Mock1Advanced reuse the archimedean scalar identity",
        ),
        (
            """  formula_matches_beta_arch := by
    intro n
    simp [referenceExactCoefficient, referenceNormalizedArchCoeff]
""",
            """  formula_matches_beta_arch := by
    intro n
    change referenceExactCoefficient n = referenceNormalizedArchCoeff n
    rfl
""",
            "Mock1Advanced compare the two constant coefficient functions directly",
        ),
        (
            """  all_residues_lt_modulus := by
    intro r hr
    simpa [referenceKloostermanDatum] using hr
""",
            """  all_residues_lt_modulus := by
    intro r hr
    change List.Mem r [0] at hr
    cases hr with
    | head _ => norm_num [referenceKloostermanDatum]
    | tail _ h => cases h
""",
            "Mock1Advanced prove the singleton Kloosterman residue bound structurally",
        ),
        (
            """def referenceCompletionShadowInstance :
    CompletionShadowInstanceCertificate where
""",
            """noncomputable def referenceCompletionShadowInstance :
    CompletionShadowInstanceCertificate where
""",
            "Mock1Advanced mark the completion-shadow instance noncomputable",
        ),
        (
            """  all_instances_named := by
    intro inst hinst
    simp at hinst
    subst inst
    exact referenceMock1NamedInstance.instanceName_nonempty
  depth_one_instance_mem := by simp
""",
            """  all_instances_named := by
    intro inst hinst
    change List.Mem inst [referenceMock1NamedInstance] at hinst
    cases hinst with
    | head _ => exact referenceMock1NamedInstance.instanceName_nonempty
    | tail _ h => cases h
  depth_one_instance_mem := List.Mem.head _
""",
            "Mock1Advanced prove the singleton named-instance registry structurally",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    # The same Rademacher-link block occurs twice.  The first replacement above
    # changes one exact instance; close the second one with its stored theorem.
    old = """  rademacher_link := by
    intro n
    rfl
"""
    new = """  rademacher_link := by
    intro n
    exact referenceNormalizedCoefficientFormula.rademacher.coeff_eq n
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced reuse the coefficient-formula Rademacher theorem")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_once(
        text,
        """  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  simpa [-SetLike.coe_sort_coe]
""",
        """  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  simp [-SetLike.coe_sort_coe]
""",
        "Mock2Advanced use Mathlib's closure-inclusion dense-range simp theorem")
    changed |= did

    text, did = replace_once(
        text,
        """inductive Gamma2Cusp
  | infinity
  | zero
  | one
  deriving DecidableEq, Fintype
""",
        """inductive Gamma2Cusp
  | infinity
  | zero
  | one
  deriving DecidableEq

instance : Fintype Gamma2Cusp where
  elems := {Gamma2Cusp.infinity, Gamma2Cusp.zero, Gamma2Cusp.one}
  complete := by
    intro k
    cases k <;> simp
""",
        "Mock2Advanced replace the fragile derived cusp Fintype by an explicit one")
    changed |= did

    text, did = replace_once(
        text,
        """  apply Set.disjoint_left.mpr
  intro τ h∞ h₀
  have hy : 1 < τ.im := by
    simpa [strictCuspHoroball] using h∞
  have hd := normSq_lt_im_of_one_lt_cuspHeight_zero τ h₀
""",
        """  apply Set.disjoint_left.mpr
  intro tau hInf hZero
  have hy : 1 < tau.im := by
    simpa [strictCuspHoroball] using hInf
  have hd := normSq_lt_im_of_one_lt_cuspHeight_zero tau hZero
""",
        "Mock2Advanced use ASCII binders in the infinity-zero disjointness proof")
    changed |= did
    text = text.replace("mul_self_nonneg τ.re, mul_self_nonneg τ.im", "mul_self_nonneg tau.re, mul_self_nonneg tau.im", 1)

    text, did = replace_once(
        text,
        """  apply Set.disjoint_left.mpr
  intro τ h∞ h₁
  have hy : 1 < τ.im := by
    simpa [strictCuspHoroball] using h∞
  have hd := normSq_sub_one_lt_im_of_one_lt_cuspHeight_one τ h₁
""",
        """  apply Set.disjoint_left.mpr
  intro tau hInf hOne
  have hy : 1 < tau.im := by
    simpa [strictCuspHoroball] using hInf
  have hd := normSq_sub_one_lt_im_of_one_lt_cuspHeight_one tau hOne
""",
        "Mock2Advanced use ASCII binders in the infinity-one disjointness proof")
    changed |= did
    text = text.replace("mul_self_nonneg (τ.re - 1), mul_self_nonneg τ.im", "mul_self_nonneg (tau.re - 1), mul_self_nonneg tau.im", 1)

    old = """  obtain ⟨Y∞, hY∞⟩ := hK.bddAbove_image
    (continuous_cuspHeight Gamma2Cusp.infinity).continuousOn
  obtain ⟨Y₀, hY₀⟩ := hK.bddAbove_image
    (continuous_cuspHeight Gamma2Cusp.zero).continuousOn
  obtain ⟨Y₁, hY₁⟩ := hK.bddAbove_image
    (continuous_cuspHeight Gamma2Cusp.one).continuousOn
  refine ⟨max Y∞ (max Y₀ Y₁), ?_⟩
"""
    new = """  obtain ⟨yInf, hyInf⟩ := hK.bddAbove_image
    (continuous_cuspHeight Gamma2Cusp.infinity).continuousOn
  obtain ⟨yZero, hyZero⟩ := hK.bddAbove_image
    (continuous_cuspHeight Gamma2Cusp.zero).continuousOn
  obtain ⟨yOne, hyOne⟩ := hK.bddAbove_image
    (continuous_cuspHeight Gamma2Cusp.one).continuousOn
  refine ⟨max yInf (max yZero yOne), ?_⟩
"""
    text, did = replace_once(text, old, new,
        "Mock2Advanced use ASCII truncation-height witnesses")
    changed |= did
    text = text.replace("(hY∞ ⟨τ, hτ, rfl⟩)", "(hyInf ⟨τ, hτ, rfl⟩)")
    text = text.replace("(hY₀ ⟨τ, hτ, rfl⟩)", "(hyZero ⟨τ, hτ, rfl⟩)")
    text = text.replace("(hY₁ ⟨τ, hτ, rfl⟩)", "(hyOne ⟨τ, hτ, rfl⟩)")

    text, did = replace_once(
        text,
        """      (by simpa [continuousMassDensity] using D.integrable κ m))
""",
        """      (by
        change Integrable
          (fun t => D.test t * Complex.normSq (D.coefficient κ m t))
          (D.spectralMeasure κ)
        exact D.integrable κ m))
""",
        "Mock2Advanced expose the continuous mass density before integrability")
    changed |= did

    text, did = replace_once(
        text,
        """  simpa [profileBesselUniformKernelEnvelope] using
    (Finset.sum_pos_iff_of_nonneg
""",
        """  simpa using
    (Finset.sum_pos_iff_of_nonneg
""",
        "Mock2Advanced remove the nonexistent profile kernel simp lemma")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2_advanced()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
