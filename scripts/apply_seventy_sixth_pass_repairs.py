from __future__ import annotations

from pathlib import Path

import apply_seventy_fifth_pass_repairs as pass75
import apply_seventy_third_pass_repairs as pass73
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def _ref_type(text: str, namespace: str, theorem: str) -> str:
    return pass75._ref_type(text, namespace, theorem)


def _conj(*types: str) -> str:
    return pass75._conj(*types)


def _forall(binder: str, typ: str) -> str:
    return pass75._forall(binder, typ)


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    spt = "SPTKernelRequirementPayloadCertificate"
    exact = "ExactCoefficientRequirementPayloadCertificate"
    padic = "PAdicRequirementPayloadCertificate"
    entropy = "EntropyReproRequirementPayloadCertificate"

    kernel_atoms = _conj(
        _ref_type(text, spt, "kernel_selection_at"),
        _ref_type(text, spt, "multiplier_phase_at"),
        _ref_type(text, spt, "cusp_convergence_at"),
        _ref_type(text, spt, "transport_across_cusps_at"),
    )
    exact_atoms = _conj(
        _ref_type(text, exact, "theta_character_at"),
        _ref_type(text, exact, "spectral_kloosterman_at"),
        _ref_type(text, exact, "local_euler_at"),
        _ref_type(text, exact, "root_filter_at"),
        _ref_type(text, exact, "paper_formula_fields_at"),
    )
    exact_coefficients = _forall(
        "n : Nat",
        _conj(
            _ref_type(text, exact, "coefficient_separation_at"),
            _ref_type(text, exact, "exact_formula_at"),
            _ref_type(text, exact, "beta_arch_formula_at"),
            _ref_type(text, exact, "beta_arch_rademacher_at"),
        ),
    )
    padic_atoms = _conj(
        _ref_type(text, padic, "face_tracking_at"),
        _ref_type(text, padic, "denominator_data_at"),
        _ref_type(text, padic, "obstruction_failure_at"),
    )
    padic_pointwise = _forall(
        "n : Nat",
        _conj(
            _ref_type(text, padic, "normalization_at"),
            _ref_type(text, padic, "overlap_at"),
            _ref_type(text, padic, "mahler_at"),
            _ref_type(text, padic, "chart_vectors_at"),
            _ref_type(text, padic, "mahler_table_at"),
        ),
    )
    padic_tail = _forall(
        "n : Nat",
        _forall(
            "hn : referenceAdvancedClaimsIICompletionCertificate."
            "padicAnalyticRange.cutoff <= n",
            _ref_type(text, padic, "tail_zero_at"),
        ),
    )
    entropy_atoms = _conj(
        _ref_type(text, entropy, "regression_cardy_at"),
        _ref_type(text, entropy, "rademacher_tail_at"),
        _ref_type(text, entropy, "entropy_cardy_wrapper_at"),
        _ref_type(text, entropy, "ols_interval_at"),
        _ref_type(text, entropy, "growth_stability_at"),
        _ref_type(text, entropy, "reproducibility_schema_at"),
    )
    entropy_degeneracy = _forall(
        "n : Nat", _ref_type(text, entropy, "degeneracy_at"))

    fields = {
        "kernel_atoms": kernel_atoms,
        "exact_atoms": exact_atoms,
        "exact_coefficients": exact_coefficients,
        "padic_atoms": padic_atoms,
        "padic_pointwise": padic_pointwise,
        "padic_tail": padic_tail,
        "entropy_atoms": entropy_atoms,
        "entropy_degeneracy": entropy_degeneracy,
    }
    applied = 0
    for field, typ in fields.items():
        text, did = pass73._replace_structure_field_type(
            text, "AdvancedClaimsIIReferenceAtomicChecklistCertificate", field, typ)
        changed |= did
        applied += int(did)

    projections = {
        "remaining_object_coefficient_at": _ref_type(
            text, "RemainingAdvancedClaimPayloadCertificate",
            "object_coefficient_schema_at"),
        "paper_registry_atoms_at": pass75._conj(
            _ref_type(text, "PaperDataInstancePayloadCertificate", "registry_eq_all_at"),
            _ref_type(text, "PaperDataInstancePayloadCertificate", "registry_name_nonempty_at"),
            _ref_type(text, "PaperDataInstancePayloadCertificate", "registry_source_nonempty_at"),
        ),
        "spt_arithmetic_atoms_at": pass75._conj(
            _ref_type(text, spt, "nat_gcd_lcm_at"),
            _ref_type(text, spt, "primewise_thickness_at"),
            _ref_type(text, spt, "valuation_certificate_at"),
            _ref_type(text, spt, "obstruction_failure_at"),
        ),
        "exact_coefficients_at": _conj(
            _ref_type(text, exact, "coefficient_separation_at"),
            _ref_type(text, exact, "exact_formula_at"),
            _ref_type(text, exact, "beta_arch_formula_at"),
            _ref_type(text, exact, "beta_arch_rademacher_at"),
        ),
        "padic_tail_at": _ref_type(text, padic, "tail_zero_at"),
        "entropy_degeneracy_at": _ref_type(text, entropy, "degeneracy_at"),
    }
    for theorem, typ in projections.items():
        text, did = pass73._replace_theorem_result(
            text, "AdvancedClaimsIIReferenceAtomicChecklistCertificate",
            theorem, typ)
        changed |= did
        applied += int(did)

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"Mock1Advanced type the remaining reference checklist batch: applied {applied}")
    else:
        print("Mock1Advanced type the remaining reference checklist batch: already applied")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """theorem wedge_add_left {p q : ℕ} (a b : ChartForm p) (c : ChartForm q) :
    wedge (a + b) c = wedge a c + wedge b c := by
  ext <;> simp [wedge] <;> ring
""",
            """theorem wedge_add_left {p q : ℕ} (a b : ChartForm p) (c : ChartForm q) :
    wedge (a + b) c = wedge a c + wedge b c := by
  apply ChartForm.ext <;> simp [wedge, chartFormAdd] <;> ring
""",
            "Mock2 stop chart-form distributivity extensionality before polynomial coefficients",
        ),
        (
            """theorem wedge_add_right {p q : ℕ} (a : ChartForm p) (b c : ChartForm q) :
    wedge a (b + c) = wedge a b + wedge a c := by
  ext <;> simp [wedge] <;> ring
""",
            """theorem wedge_add_right {p q : ℕ} (a : ChartForm p) (b c : ChartForm q) :
    wedge a (b + c) = wedge a b + wedge a c := by
  apply ChartForm.ext <;> simp [wedge, chartFormAdd] <;> ring
""",
            "Mock2 stop right distributivity extensionality before polynomial coefficients",
        ),
        (
            """      wedge a (wedge b c) := by
  ext <;> simp [wedge] <;> ring
""",
            """      wedge a (wedge b c) := by
  apply ChartForm.ext <;> simp [GradedForm.cast, wedge] <;> ring
""",
            "Mock2 prove wedge associativity at the four polynomial fields",
        ),
        (
            """def differential {n : ℕ} (a : ChartForm n) : ChartForm (n + 1) where
""",
            """noncomputable def differential {n : ℕ} (a : ChartForm n) : ChartForm (n + 1) where
""",
            "Mock2 mark the polynomial derivative chart differential noncomputable",
        ),
        (
            """def differentialHom (n : ℕ) : ChartForm n →+ ChartForm (n + 1) where
""",
            """noncomputable def differentialHom (n : ℕ) : ChartForm n →+ ChartForm (n + 1) where
""",
            "Mock2 mark the bundled chart differential noncomputable",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [show (-1 : ZMod 2) = 1 by decide]
""",
            """  rw [CongruenceSubgroup.Gamma_mem]
  norm_num
  change (-1 : ZMod 2) = 1
  decide
""",
            "Mock2Advanced close the remaining characteristic-two diagonal entry",
        ),
        (
            """def HasOrderedSum (f : ℕ → ℂ) (z : ℂ) : Prop :=
  Tendsto (fun N => ∑ n in Finset.range (N + 1), f n) atTop (𝓝 z)
""",
            """def HasOrderedSum (f : ℕ → ℂ) (z : ℂ) : Prop :=
  Tendsto (fun N => Finset.sum (Finset.range (N + 1)) f) atTop (𝓝 z)
""",
            "Mock2Advanced spell out the ordered partial sum without parser-sensitive notation",
        ),
        (
            """def prefixSum (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n in Finset.range (N + 1), a n
""",
            """def prefixSum (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  Finset.sum (Finset.range (N + 1)) a
""",
            "Mock2Advanced spell out prefixSum with Finset.sum",
        ),
        (
            """    (∑ n in Finset.range (N + 1), a n * b n) =
      prefixSum a N * b N +
        ∑ n in Finset.range N, abelRemainder a b n := by
""",
            """    Finset.sum (Finset.range (N + 1)) (fun n => a n * b n) =
      prefixSum a N * b N +
        Finset.sum (Finset.range N) (abelRemainder a b) := by
""",
            "Mock2Advanced spell out both finite Abel sums",
        ),
        (
            """        (fun N => ∑ n in Finset.range N, abelRemainder a b n)
""",
            """        (fun N => Finset.sum (Finset.range N) (abelRemainder a b))
""",
            "Mock2Advanced spell out the remainder partial sums",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
""",
            """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  field_simp [ModularForm.eta_ne_zero (δ • z).2]
""",
            "FunctionalAnalysis clear the final intermediate eta denominator",
        ),
        (
            """noncomputable instance gammaTwoCountable : Countable GammaTwo :=
  Countable.of_injective
    (fun γ : GammaTwo =>
      ((((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
       (((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
       (((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
       (((γ : GammaTwo) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1))
    (by
      intro a b h
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      funext i j
      fin_cases i <;> fin_cases j <;> simp_all)
""",
            """noncomputable instance gammaTwoCountable : Countable GammaTwo := by
  infer_instance
""",
            "FunctionalAnalysis use the inherited countability of the matrix subgroup",
        ),
        (
            """theorem gammaTwoToSL2Real_isClosedEmbedding :
    IsClosedEmbedding gammaTwoToSL2Real := by
""",
            """theorem gammaTwoToSL2Real_isClosedEmbedding :
    Topology.IsClosedEmbedding gammaTwoToSL2Real := by
""",
            "FunctionalAnalysis use the current Topology namespace for closed embeddings",
        ),
        (
            """    intro z
    change gammaTwoEffectiveElement γ z = a z
    exact (hγ z).symm
""",
            """    intro z
    change γ • z = a • z
    exact (hγ z).symm
""",
            "FunctionalAnalysis compare effective permutations through their actions",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass75.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
