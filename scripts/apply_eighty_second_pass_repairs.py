from __future__ import annotations

from pathlib import Path
import re

import apply_seventy_eighth_pass_repairs as pass78
import apply_seventy_ninth_pass_repairs as pass79
import apply_eightieth_pass_repairs as pass80
import apply_seventy_fifth_pass_repairs as pass75
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


PAYLOAD_NAMESPACES = {
    "PaperDataInstancePayloadCertificate",
    "RemainingAdvancedClaimPayloadCertificate",
    "SPTKernelRequirementPayloadCertificate",
    "ExactCoefficientRequirementPayloadCertificate",
    "PAdicRequirementPayloadCertificate",
    "EntropyReproRequirementPayloadCertificate",
}


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("Formula-level prompt atoms.")
    end_marker = text.find("\n/-!", start + 40)
    end = len(text) if end_marker < 0 else end_marker
    block = text[start:end]
    names = re.findall(
        r"(?m)^theorem (reference_formula_level_prompt_[A-Za-z0-9_]+)",
        block,
    )
    applied = 0
    for name in names:
        pos = text.index(f"theorem {name}", start)
        assignment = text.index(" :=\n", pos)
        signature = text[pos:assignment]
        refs = [
            (namespace, theorem)
            for namespace, theorem in re.findall(
                r"([A-Za-z0-9_]+Certificate)\.([A-Za-z0-9_]+)",
                signature,
            )
            if namespace in PAYLOAD_NAMESPACES
        ]
        if not refs:
            continue
        types = [pass75._ref_type(text, namespace, theorem)
                 for namespace, theorem in refs]
        result_type = types[0] if len(types) == 1 else pass75._conj(*types)

        result_offset = None
        offset = 0
        for line in signature.splitlines(keepends=True):
            stripped = line.rstrip()
            if stripped.endswith(") :") or (
                line.startswith(f"theorem {name}") and stripped.endswith(":")
            ):
                result_offset = offset + line.rfind(":") + 1
            offset += len(line)
        if result_offset is None:
            raise RuntimeError(f"Mock1Advanced {name}: result delimiter absent")
        absolute = pos + result_offset
        rendered = "\n" + pass71._render_type(result_type)
        if text[absolute:assignment] != rendered:
            text = text[:absolute] + rendered + text[assignment:]
            changed = True
            applied += 1

    old = "theorem reference_advanced_claims_ii_reference_atomic_checklist :\n"
    new = "noncomputable def reference_advanced_claims_ii_reference_atomic_checklist :\n"
    if old in text:
        text = text.replace(old, new, 1)
        changed = True

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"Mock1Advanced restore explicit formula-atom proposition types: applied {applied}")
    else:
        print("Mock1Advanced restore explicit formula-atom proposition types: already applied")


def repair_mock2() -> None:
    pass79.repair_mock2()
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """theorem wedge_left_matrix (U : TopologicalSpace.Opens X) (g A B : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U (g * A) B) =
      g * (show Ω U from (G.toCurvatureAlgebra).wedge U A B) := by
  simpa only [toCurvatureAlgebra] using (mul_assoc g A B)
""",
        """theorem wedge_left_matrix (U : TopologicalSpace.Opens X) (g A B : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U (g * A) B) =
      g * (show Ω U from (G.toCurvatureAlgebra).wedge U A B) := by
  change (g * A) * B = g * (A * B)
  exact mul_assoc g A B
""",
        1,
        "Mock2 unfold the left wedge adapter to matrix multiplication",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """theorem wedge_right_matrix (U : TopologicalSpace.Opens X) (A B g : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U A (B * g)) =
      (show Ω U from (G.toCurvatureAlgebra).wedge U A B) * g := by
  simpa only [toCurvatureAlgebra] using (mul_assoc A B g).symm
""",
        """theorem wedge_right_matrix (U : TopologicalSpace.Opens X) (A B g : Ω U) :
    (show Ω U from (G.toCurvatureAlgebra).wedge U A (B * g)) =
      (show Ω U from (G.toCurvatureAlgebra).wedge U A B) * g := by
  change A * (B * g) = (A * B) * g
  exact (mul_assoc A B g).symm
""",
        1,
        "Mock2 unfold the right wedge adapter to matrix multiplication",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    pass80.repair_mock2_advanced()
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """        exact (M.core_equivariant v hv).isAE)
""",
        """        exact (M.core_equivariant v hv).isAE μ)
""",
        1,
        "Mock2Advanced supply the measure to the a.e. automorphy projection",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      simp only [abelRemainder] at ih ⊢
      ring
""",
        """  | succ N ih =>
      unfold abelRemainder at ih ⊢
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      ring
""",
        1,
        "Mock2Advanced unfold Abel remainders before rewriting the induction hypothesis",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    pass79.repair_functional_analysis()
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  calc
    (ModularForm.eta ↑(γ • δ • z))⁻¹ =
        1 * (ModularForm.eta ↑(γ • δ • z))⁻¹ := by rw [one_mul]
    _ =
        (ModularForm.eta ↑(δ • z) *
          (ModularForm.eta ↑(δ • z))⁻¹) *
            (ModularForm.eta ↑(γ • δ • z))⁻¹ := by
      rw [mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2)]
    _ =
        ModularForm.eta ↑(δ • z) *
          ((ModularForm.eta ↑(δ • z))⁻¹ *
            (ModularForm.eta ↑(γ • δ • z))⁻¹) := by rw [mul_assoc]
""",
        """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2] <;>
    field_simp [ModularForm.eta_ne_zero z.2,
      ModularForm.eta_ne_zero (δ • z).2,
      ModularForm.eta_ne_zero ((γ * δ) • z).2] <;> ring
""",
        1,
        "FunctionalAnalysis clear both layers of the inverse-eta denominators",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass78.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
