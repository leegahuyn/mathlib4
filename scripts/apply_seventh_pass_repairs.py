from __future__ import annotations

import re
from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied/source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def repair_spt2() -> None:
    path = ROOT / "Spt2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  apply Algebra.Extension.Cotangent.ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  rw [hprincipal, hmap, quotientSpanCotangentEquivKer_toCotangent]
  congr 1
  apply Subtype.ext
  rfl
"""
    new = """  apply Algebra.Extension.Cotangent.ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  change (Algebra.Extension.Cotangent.of
      (quotientSpanCotangentEquivKer f
        (principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a)))).val =
    (Algebra.Extension.Cotangent.mk
      (P := quotientExtension f)
      ⟨a * f, by
        rw [quotientExtension_ker]
        exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩).val
  rw [hprincipal, hmap, quotientSpanCotangentEquivKer_toCotangent]
  congr 1
"""
    text, did = replace_once(text, old, new,
        "Spt2 normalize quotient representative before rewriting")
    changed |= did

    old = """  rw [hprincipal, hmap, quotientSpanCotangentEquivKer_toCotangent]
  congr 1
  apply Subtype.ext
  rfl
"""
    new = """  rw [hprincipal, hmap, quotientSpanCotangentEquivKer_toCotangent]
  congr 1
"""
    text, did = replace_once(text, old, new,
        "Spt2 remove tactics after congr closes the goal")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1() -> None:
    path = ROOT / "Mock1.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    anchor = "import Mathlib.LinearAlgebra.Matrix.NonsingularInverse\n"
    if "import Mathlib.LinearAlgebra.Matrix.Rank\n" not in text and anchor in text:
        text = text.replace(anchor, anchor + "import Mathlib.LinearAlgebra.Matrix.Rank\n", 1)
        changed = True
        print("Mock1 import current Matrix.rank API: applied")

    old = """  simpa [finiteMahlerEvalSMul] using
    (PadicInt.mahlerSeries_apply_nat (p := p) (a := a) ha
      (m := m) (n := N) hmN)
"""
    new = """  simpa [finiteMahlerEvalSMul, ← Fin.sum_univ_eq_sum_range,
    Nat.cast_smul_eq_nsmul] using
    (PadicInt.mahlerSeries_apply_nat (p := p) (a := a) ha
      (m := m) (n := N) hmN)
"""
    text, did = replace_once(text, old, new,
        "Mock1 convert Mahler range sum and scalar action")
    changed |= did

    old = """          intro j _hj
          rw [B.initial_segment j]
"""
    new = """          intro j _hj
          change (Nat.choose n.val j.val : ℤ_[p]) • B.infiniteCoeffs j.val =
            (Nat.choose n.val j.val : ℤ_[p]) • finiteDifferenceCoeff B.samples j
          rw [B.initial_segment j]
"""
    text, did = replace_once(text, old, new,
        "Mock1 expose Mahler coefficient under eta reduction")
    changed |= did

    count = text.count("coe_lcm_dvd_iff")
    if count:
        text = text.replace("coe_lcm_dvd_iff", "lcm_dvd_iff")
        changed = True
        print(f"Mock1 use integer lcm divisibility API: applied {count}")

    old = """  · intro h i j n
    rw [h i j]
    simp [CechDiff]
"""
    new = """  · intro h i j n
    simp [CechDiff, h i j]
"""
    text, did = replace_once(text, old, new,
        "Mock1 pairwise Cech difference proof")
    changed |= did

    old = """  · rintro ⟨g, hg⟩ i j n
    rw [hg i, hg j]
    simp [CechDiff]
"""
    new = """  · rintro ⟨g, hg⟩ i j n
    simp [CechDiff, hg i, hg j]
"""
    text, did = replace_once(text, old, new,
        "Mock1 global Cech difference proof")
    changed |= did

    text2 = text.replace(
        "(CechDiff s i j n : ZMod pk)",
        "(CechDiff (R := ℤ) s i j n : ZMod pk)")
    text2 = text2.replace(
        "CechObstructionCocycle M pk (CechDiff s) hker",
        "CechObstructionCocycle M pk (CechDiff (R := ℤ) s) hker")
    if text2 != text:
        text = text2
        changed = True
        print("Mock1 make Cech coefficient ring explicit")

    for name in ["D4GateCertificate_of_lcm_overlap",
                 "D4GateCertificate_of_modular_padic_congruence"]:
        text2, n = re.subn(rf"(?m)^theorem {name}\b", f"noncomputable def {name}", text, count=1)
        if n:
            text = text2
            changed = True
            print(f"Mock1 {name}: changed theorem to data definition")

    old = """theorem halfAlpha_formula (base alpha : ℚ) :
    base * (alpha / 2) ^ 2 = (base * scale halfAlpha) * alpha ^ 2 := by
  ring
"""
    new = """theorem halfAlpha_formula (base alpha : ℚ) :
    base * (alpha / 2) ^ 2 = (base * scale halfAlpha) * alpha ^ 2 := by
  rw [halfAlpha_scale]
  ring
"""
    text, did = replace_once(text, old, new,
        "Mock1 unfold half-alpha Cardy scale")
    changed |= did

    old = """  intro b
  rw [A_inftyMatrix_mulVec_eq_A_infty_mul, A_infty_exact_solve]
"""
    new = """  intro b
  change A_inftyMatrix.mulVec (A_infty_solve b) = b
  rw [A_inftyMatrix_mulVec_eq_A_infty_mul, A_infty_exact_solve]
"""
    text, did = replace_once(text, old, new,
        "Mock1 expose matrix multiplication in full-row-rank witness")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  cases layer <;> cases item <;>
    simp_all [requestedDefinitions, RequestedDefinitionItem.integratedLayer]
"""
    new = """  cases layer <;> cases item <;>
    simp_all only [requestedDefinitions, RequestedDefinitionItem.integratedLayer,
      List.mem_cons, List.not_mem_nil]
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced layer soundness with explicit list membership")
    changed |= did

    old = """  cases layer <;> cases item <;>
    simp_all [requestedDefinitions, RequestedDefinitionItem.primaryObjective,
      objectives]
"""
    new = """  cases layer <;> cases item <;>
    simp_all only [requestedDefinitions, RequestedDefinitionItem.primaryObjective,
      objectives, List.mem_cons, List.not_mem_nil]
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced objective soundness with explicit list membership")
    changed |= did

    old = """  cases item <;>
    simp [requestedDefinitions, RequestedDefinitionItem.integratedLayer]
"""
    new = """  cases item <;>
    decide
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced requested definition placement by kernel decision")
    changed |= did

    old = """structure RequestedDefinitionLayerMatrix {X : Type*}
    (B : UnconditionalCertificationBundle X) : Prop where
"""
    new = """structure RequestedDefinitionLayerMatrix {X : Type*}
    (B : UnconditionalCertificationBundle X) where
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced make layer matrix a data structure")
    changed |= did

    data_names = {
        "manifest_at", "reference_requested_layer_blueprint",
        "reference_local_audit_manifest", "reference_environment_pin_manifest",
        "environment_at", "local_audit_at", "file_manifest_at", "layer_blueprint_at",
        "reference_lake_project_lock_certificate", "reference_unconditionality_policy",
        "environment_pin_at", "project_lock_at", "unconditionality_at",
        "reference_axiom_audit_complete", "reference_axiom_audit_project_lock",
        "reference_axiom_audit_file_manifest", "reference_axiom_audit_local_manifest",
        "reference_axiom_audit_environment_pin", "reference_axiom_audit_unconditionality",
        "policy_at", "reference_certification_readiness", "readiness_at",
        "requested_definition_layer_matrix", "reference_requested_definition_layer_matrix",
        "requested_definition_layer_matrix_at",
        "reference_readiness_requested_definition_layer_matrix",
    }
    for name in sorted(data_names, key=len, reverse=True):
        text2, n = re.subn(rf"(?m)^theorem {re.escape(name)}\b",
            f"noncomputable def {name}", text)
        if n:
            text = text2
            changed = True
            print(f"Mock1Advanced {name}: changed {n} data theorem declaration(s)")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text2, n = re.subn(r"(?m)^def PhiCokernel \(M N : ℕ\) : Type :=",
        "abbrev PhiCokernel (M N : ℕ) : Type :=", text, count=1)
    if n:
        text = text2
        changed = True
        print("Mock2 expose quotient cokernel instances through abbrev")

    old = """  have hx0 : x = 0 := by
    apply intersectionIdealIncl_injective M N
    simpa only [map_zero] using hx
  subst x
  refine ⟨0, ?_⟩
  simp [leftEndpoint, zeroToIntersection]
"""
    new = """  have hx0 : x = 0 := by
    apply intersectionIdealIncl_injective M N
    exact hx.trans (map_zero (intersectionIdealIncl M N)).symm
  subst x
  refine ⟨0, ?_⟩
  rfl
"""
    text, did = replace_once(text, old, new,
        "Mock2 literal left-endpoint exactness")
    changed |= did

    old = """theorem quotientMap_comp_Phi_eq_zero (M N : ℕ) :
    (quotientMap M N).comp (Phi M N) = 0 := by
  ext z
"""
    new = """theorem quotientMap_comp_Phi_eq_zero (M N : ℕ) :
    (quotientMap M N).comp (Phi M N) = 0 := by
  apply AddMonoidHom.ext
  intro z
"""
    text, did = replace_once(text, old, new,
        "Mock2 quotient-map composite extensionality")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_spt2()
    repair_mock1()
    repair_mock1_advanced()
    repair_mock2()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
