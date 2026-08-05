from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirtieth_pass_repairs as pass130
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


def repair_mock1_advanced() -> None:
    apply_replacements(ROOT / "Mock1_Advanced.lean", [
        (
            """theorem reference_advanced_claims_ii_abstract_concrete_certification_bridge :
    AdvancedClaimsIIAbstractConcreteCertificationBridgeCertificate where
""",
            """noncomputable def reference_advanced_claims_ii_abstract_concrete_certification_bridge :
    AdvancedClaimsIIAbstractConcreteCertificationBridgeCertificate where
""",
            1,
            "Mock1Advanced define the data-bearing abstract-concrete bridge",
        ),
        (
            """structure AdvancedClaimsIISectionCertificationBridgeCertificate : Prop where
""",
            """structure AdvancedClaimsIISectionCertificationBridgeCertificate : Type where
""",
            1,
            "Mock1Advanced place the data-bearing section certification bridge in Type",
        ),
        (
            """theorem reference_advanced_claims_ii_section_certification_bridge :
    AdvancedClaimsIISectionCertificationBridgeCertificate where
""",
            """noncomputable def reference_advanced_claims_ii_section_certification_bridge :
    AdvancedClaimsIISectionCertificationBridgeCertificate where
""",
            1,
            "Mock1Advanced define the data-bearing section certification bridge",
        ),
        (
            """    Prop where
  section_certification :
    AdvancedClaimsIISectionCertificationBridgeCertificate
""",
            """    Type where
  section_certification :
    AdvancedClaimsIISectionCertificationBridgeCertificate
""",
            1,
            "Mock1Advanced place the data-bearing section leaf discharge in Type",
        ),
        (
            """theorem reference_advanced_claims_ii_section_leaf_discharge
""",
            """noncomputable def reference_advanced_claims_ii_section_leaf_discharge
""",
            1,
            "Mock1Advanced define the data-bearing section leaf discharge",
        ),
        (
            """theorem ramanujan_f_actual_constructor_boundary_at
""",
            """noncomputable def ramanujan_f_actual_constructor_boundary_at
""",
            1,
            "Mock1Advanced define the data-valued Ramanujan constructor projection",
        ),
        (
            """theorem reference_advanced_claims_ii_microlocal_certification_readiness
""",
            """noncomputable def reference_advanced_claims_ii_microlocal_certification_readiness
""",
            1,
            "Mock1Advanced define the data-bearing microlocal readiness package",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """abbrev TensorSection (L M : LinearPresheaf X)
""",
            """abbrev TensorSection (L M : LinearPresheaf.{u, v} X)
""",
            1,
            "Mock2 synchronize tensor-section presheaf universes",
        ),
        (
            """def tensorRestriction (L M : LinearPresheaf X)
""",
            """def tensorRestriction (L M : LinearPresheaf.{u, v} X)
""",
            1,
            "Mock2 synchronize tensor restriction universes",
        ),
        (
            """def tensorPresheaf (L M : LinearPresheaf X) : LinearPresheaf X where
  obj U := ModuleCat.of ℂ (TensorSection L M U)
""",
            """def tensorPresheaf (L M : LinearPresheaf.{u, v} X) :
    LinearPresheaf.{u, v} X where
  obj U := ModuleCat.of.{max u v, 0} ℂ (TensorSection L M U)
""",
            1,
            "Mock2 fix the pointwise tensor presheaf output universe",
        ),
        (
            """theorem tensor_fibre_has_module (L M : LinearPresheaf X)
""",
            """noncomputable def tensor_fibre_has_module (L M : LinearPresheaf X)
""",
            1,
            "Mock2 define the tensor fibre module witness rather than stating it as a theorem",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """    exact Finset.single_le_sum
      (fun κ _ => integral_nonneg fun t =>
        Complex.normSq_nonneg (D.coefficient κ m t))
      (Finset.mem_univ A.activeCusp)
""",
            """    exact Finset.single_le_sum
      (f := fun κ : Gamma2Cusp =>
        ∫ t in A.window κ, f κ t)
      (fun κ _ => integral_nonneg fun t =>
        Complex.normSq_nonneg (D.coefficient κ m t))
      (Finset.mem_univ A.activeCusp)
""",
            1,
            "Mock2Advanced determine the real finite-sum function explicitly",
        ),
        (
            """    simpa [rawWindowActivity] using B.lower_rawActivity m hm
""",
            """    simpa [rawActivityForWindow] using B.lower_rawActivity m hm
""",
            1,
            "Mock2Advanced unfold the actual raw activity expression in the certificate field",
        ),
        (
            """    (hπ : ∀ g x, π (g • x) = π x)
""",
            """    (hπ : ∀ (g : G) (x : X), π (g • x) = π x)
""",
            2,
            "Mock2Advanced type both invariant-map action arguments explicitly",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """def gammaTwoVerticalIncidencePolynomial
""",
            """noncomputable def gammaTwoVerticalIncidencePolynomial
""",
            1,
            "FunctionalAnalysis mark the vertical polynomial definition noncomputable",
        ),
        (
            """def gammaTwoCircularIncidencePolynomial
""",
            """noncomputable def gammaTwoCircularIncidencePolynomial
""",
            1,
            "FunctionalAnalysis mark the circular polynomial definition noncomputable",
        ),
        (
            """    simpa [gammaTwoVerticalIncidencePolynomial, hc] using hcoeff
""",
            """    norm_num [gammaTwoVerticalIncidencePolynomial, hc] at hcoeff
""",
            1,
            "FunctionalAnalysis compute the vertical linear coefficient in the zero-c case",
        ),
        (
            """    exact hlead (by
      simpa [gammaTwoVerticalIncidencePolynomial] using hcoeff)
""",
            """    apply hlead
    norm_num [gammaTwoVerticalIncidencePolynomial] at hcoeff ⊢
    exact hcoeff
""",
            1,
            "FunctionalAnalysis compute the vertical quadratic coefficient explicitly",
        ),
        (
            """  exact hlead (by
    simpa [gammaTwoCircularIncidencePolynomial] using hcoeff)
""",
            """  apply hlead
  norm_num [gammaTwoCircularIncidencePolynomial] at hcoeff ⊢
  exact hcoeff
""",
            1,
            "FunctionalAnalysis compute the circular quadratic coefficient explicitly",
        ),
        (
            """  rw [Polynomial.IsRoot.def,
    gammaTwoCircularIncidencePolynomial_eval]
""",
            """  change Polynomial.eval (t : ℝ)
      (gammaTwoCircularIncidencePolynomial
        (gammaTwoCuspLevel Y)
        (gammaTwoCornerLowerLeft (e, .circularArc) q ^ 2 +
          gammaTwoCornerLowerRight (e, .circularArc) q ^ 2)
        (gammaTwoCornerLowerLeft (e, .circularArc) q *
          gammaTwoCornerLowerRight (e, .circularArc) q)) = 0
  rw [gammaTwoCircularIncidencePolynomial_eval]
""",
            1,
            "FunctionalAnalysis expose the circular root goal as polynomial evaluation",
        ),
        (
            """  rw [Polynomial.IsRoot.def,
    gammaTwoVerticalIncidencePolynomial_eval]
""",
            """  change Polynomial.eval (t : ℝ)
      (gammaTwoVerticalIncidencePolynomial
        (gammaTwoCuspLevel Y)
        (gammaTwoCornerLowerLeft (e, .leftVerticalSegment) q)
        (gammaTwoCornerLowerRight (e, .leftVerticalSegment) q)
        (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2)) = 0
  rw [gammaTwoVerticalIncidencePolynomial_eval]
""",
            1,
            "FunctionalAnalysis expose the left vertical root goal as polynomial evaluation",
        ),
        (
            """  rw [Polynomial.IsRoot.def,
    gammaTwoVerticalIncidencePolynomial_eval]
""",
            """  change Polynomial.eval (t : ℝ)
      (gammaTwoVerticalIncidencePolynomial
        (gammaTwoCuspLevel Y)
        (gammaTwoCornerLowerLeft (e, .rightVerticalSegment) q)
        (gammaTwoCornerLowerRight (e, .rightVerticalSegment) q)
        ((1 : ℝ) / 2) (Real.sqrt 3 / 2)) = 0
  rw [gammaTwoVerticalIncidencePolynomial_eval]
""",
            1,
            "FunctionalAnalysis expose the right vertical root goal as polynomial evaluation",
        ),
    ])


def main() -> int:
    pass130.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
