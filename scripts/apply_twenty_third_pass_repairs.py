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

    constructors = [
        "paperClaims", "paperSymbols", "paperData", "paperTables", "protocol",
        "principalPart", "principalPartExponent", "cuspTransport", "spt", "sptCRT",
        "muKernel", "muKernelPaper", "rademacher", "rademacherTail", "kernelCusp",
        "betaArchimedean", "exactCoefficient", "pAdic", "pAdicMahler", "regression",
        "entropyCardy", "advanced", "paperInstances",
    ]
    cases = []
    for depth, ctor in enumerate(constructors):
        proof = "List.Mem.head _"
        for _ in range(depth):
            proof = f"List.Mem.tail _ ({proof})"
        cases.append(f"  | {ctor} => exact {proof}")
    old = """theorem mem_all (m : PaperInfrastructureModule) :
    List.Mem m all := by
  cases m <;> decide
"""
    new = """theorem mem_all (m : PaperInfrastructureModule) :
    List.Mem m all := by
  cases m with
""" + "\n".join(cases) + "\n"
    text, did = replace_once(text, old, new,
        "Mock1Advanced prove all paper-module memberships structurally")
    changed |= did

    for old_decl, new_decl, label in [
        ("def reference_paper_infrastructure_protocol :\n",
         "noncomputable def reference_paper_infrastructure_protocol :\n",
         "Mock1Advanced protocol alias inherits noncomputability"),
        ("def reference_paper_infrastructure_data_schema :\n",
         "noncomputable def reference_paper_infrastructure_data_schema :\n",
         "Mock1Advanced data-schema alias inherits noncomputability"),
    ]:
        text, did = replace_once(text, old_decl, new_decl, label)
        changed |= did

    for old_name, new_name, label in [
        (".paperSectionName", ".sectionName",
         "Mock1Advanced restore unrelated sectionName projections"),
        ("PaperSection.paperSection", "PaperSection.section",
         "Mock1Advanced restore PaperSection constructor names"),
        (".paperSection_eq", ".section_eq",
         "Mock1Advanced restore unrelated section equality projections"),
    ]:
        count = text.count(old_name)
        if count:
            text = text.replace(old_name, new_name)
            changed = True
            print(f"{label}: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        ("""  comm₁₂ := by
    simpa using (zero_comp
      (AddCommGrpCat.ofHom (intersectionRestriction hM hN)))
""",
         """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    simp
""",
         "Mock2 prove the left zero square on underlying homomorphisms"),
        ("""  comm₂₃ := by
    simpa using (comp_zero
      (AddCommGrpCat.ofHom (gcdRestriction hM hN)))
""",
         """  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    simp
""",
         "Mock2 prove the standard right zero square on underlying homomorphisms"),
        ("""  comm₂₃ := by
    simpa using (comp_zero
      (AddCommGrpCat.ofHom (cokernelMap hM hN)))
""",
         """  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    simp
""",
         "Mock2 prove the actual right zero square on underlying homomorphisms"),
        ("""theorem quotientStepIntegerHom_gcd_eq_zero (M N : ℕ) :
    quotientStepIntegerHom M N (Nat.gcd M N : ℤ) = 0 := by
  change (quotientStep M N : ZMod N) *
    (Nat.gcd M N : ZMod N) = 0
  rw [← Nat.cast_mul, quotientStep_mul_gcd, ZMod.natCast_self]
""",
         """theorem quotientStepIntegerHom_gcd_eq_zero (M N : ℕ) :
    quotientStepIntegerHom M N (Nat.gcd M N : ℤ) = 0 := by
  rw [quotientStepIntegerHom_apply, ← Nat.cast_mul,
    quotientStep_mul_gcd, ZMod.natCast_self]
""",
         "Mock2 expose quotient-step application before the gcd calculation"),
        ("""@[simp] theorem gcdToKernelHom_intCast
    (M N : ℕ) (z : ℤ) :
    (gcdToKernelHom M N (z : ZMod (Nat.gcd M N)) : ZMod N) =
      (quotientStep M N : ZMod N) * (z : ZMod N) := by
  simp
""",
         """@[simp] theorem gcdToKernelHom_intCast
    (M N : ℕ) (z : ℤ) :
    (gcdToKernelHom M N (z : ZMod (Nat.gcd M N)) : ZMod N) =
      (quotientStep M N : ZMod N) * (z : ZMod N) := by
  exact quotientToAmbientHom_intCast M N z
""",
         "Mock2 reuse the ambient integer-cast formula directly"),
    ]
    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """        ENNReal.ofNNReal ((1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2) := by
"""
    new = """        ENNReal.ofNNReal (((1 : NNReal) /
          (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2) := by
"""
    text, changed = replace_once(text, old, new,
        "Mock2Advanced type the NNReal numerator explicitly")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_once(
        text,
        """section Realification

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
""",
        """section Realification

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
""",
        "FunctionalAnalysis scope the realification elaboration budget")
    changed |= did

    count = text.count("  set_option maxHeartbeats 800000 in\n  set_option maxRecDepth 100000 in\n")
    if count:
        text = text.replace(
            "  set_option maxHeartbeats 800000 in\n  set_option maxRecDepth 100000 in\n", "")
        changed = True
        print(f"FunctionalAnalysis remove ineffective nested definition budgets: applied {count}")

    text, did = replace_once(
        text,
        """section RecoverComplexEquation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
""",
        """section RecoverComplexEquation

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
""",
        "FunctionalAnalysis scope the complex-recovery elaboration budget")
    changed |= did

    count = text.count("  set_option maxHeartbeats 800000 maxRecDepth 100000 in\n")
    if count:
        text = text.replace(
            "  set_option maxHeartbeats 800000 maxRecDepth 100000 in\n", "")
        changed = True
        print(f"FunctionalAnalysis remove invalid multi-option proof command: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
