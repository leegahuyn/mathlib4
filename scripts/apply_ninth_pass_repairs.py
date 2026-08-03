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


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem mem_all (cmd : LocalAuditCommand) :
    List.Mem cmd all := by
  cases cmd <;> simp [all]
"""
    new = """theorem mem_all (cmd : LocalAuditCommand) :
    List.Mem cmd all := by
  cases cmd with
  | leanFileCheck => exact List.Mem.head _
  | printAxiomsAudit => exact List.Mem.tail _ (List.Mem.head _)
  | staticTextScan => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | hashSnapshot =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced local audit command membership")
    changed |= did

    old = """theorem printAxiomsAudit_covers_layer
    (layer : AxiomAuditLayer) :
    List.Mem layer (auditLayers LocalAuditCommand.printAxiomsAudit) := by
  cases layer <;> simp [auditLayers]
"""
    tails = {
        "domain": 0, "qseries": 1, "muKernel": 2, "slash": 3,
        "linear": 4, "entropy": 5, "rademacher": 6,
        "degeneracy": 7, "sptTor": 8, "padicMahler": 9,
        "regression": 10, "coverage": 11, "reference": 12,
    }
    cases = []
    for ctor, depth in tails.items():
        proof = "List.Mem.head _"
        for _ in range(depth):
            proof = f"List.Mem.tail _ ({proof})"
        cases.append(f"  | {ctor} => exact {proof}")
    new = """theorem printAxiomsAudit_covers_layer
    (layer : AxiomAuditLayer) :
    List.Mem layer (auditLayers LocalAuditCommand.printAxiomsAudit) := by
  cases layer with
""" + "\n".join(cases) + "\n"
    text, did = replace_once(text, old, new,
        "Mock1Advanced print-axioms coverage")
    changed |= did

    text2, n = re.subn(r"(?m)^(\s*)seal\s*:", r"\1«seal» :", text)
    if n:
        text = text2
        changed = True
        print(f"Mock1Advanced escape seal fields: applied {n}")
    text2, n = re.subn(r"(?m)^(\s*)seal\s*:=", r"\1«seal» :=", text)
    if n:
        text = text2
        changed = True
        print(f"Mock1Advanced escape seal constructors: applied {n}")
    text2, n = re.subn(r"\.seal\b", ".«seal»", text)
    if n:
        text = text2
        changed = True
        print(f"Mock1Advanced escape seal projections: applied {n}")

    for name in ["reference_end_to_end_certification_evidence",
                 "reference_mock1_advanced_compatibility"]:
        text2, n = re.subn(rf"(?m)^theorem {name}\b",
            f"noncomputable def {name}", text, count=1)
        if n:
            text = text2
            changed = True
            print(f"Mock1Advanced {name}: changed data theorem to definition")

    text2 = text.replace(
        "C.corollary1_holomorphic Fminus R S hsplit hS",
        "C.corollary1_holomorphic (X := X) Fminus R S hsplit hS")
    text2 = text2.replace(
        "C.shadow_zero xiFhat g S kappa hshadow hS",
        "C.shadow_zero (X := X) xiFhat g S kappa hshadow hS")
    text2 = text2.replace(
        "referenceMock1AdvancedCompatibilityCertificate.corollary1_holomorphic_at\n    Fminus R S hsplit hS",
        "referenceMock1AdvancedCompatibilityCertificate.corollary1_holomorphic_at\n    (X := X) Fminus R S hsplit hS")
    text2 = text2.replace(
        "referenceMock1AdvancedCompatibilityCertificate.shadow_zero_at\n    xiFhat g S kappa hshadow hS",
        "referenceMock1AdvancedCompatibilityCertificate.shadow_zero_at\n    (X := X) xiFhat g S kappa hshadow hS")
    if text2 != text:
        text = text2
        changed = True
        print("Mock1Advanced make compatibility universe arguments explicit")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    pairs = [
      ("""theorem comparison_comp_quotientMorphism (M N : ℕ) :
    Prop21StandardSequence.comparison M N ≫ quotientMorphism M N = 0 := by
  apply AddCommGrpCat.hom_ext
  simpa [Prop21StandardSequence.comparison, quotientMorphism] using
    (quotientMap_comp_Phi_eq_zero M N)
""",
       """theorem comparison_comp_quotientMorphism (M N : ℕ) :
    Prop21StandardSequence.comparison M N ≫ quotientMorphism M N = 0 := by
  apply AddCommGrpCat.hom_ext
  change (quotientMap M N).comp (Phi M N) = 0
  exact quotientMap_comp_Phi_eq_zero M N
""", "categorical quotient relation"),
      ("""theorem quotientMorphism_comp_gcdIso_hom (M N : ℕ) :
    quotientMorphism M N ≫ (gcdIso M N).hom =
      Prop21StandardSequence.difference M N := by
  apply AddCommGrpCat.hom_ext
  simpa [quotientMorphism, gcdIso, Prop21StandardSequence.difference] using
    (equivZMod_toAddMonoidHom_comp_quotientMap M N)
""",
       """theorem quotientMorphism_comp_gcdIso_hom (M N : ℕ) :
    quotientMorphism M N ≫ (gcdIso M N).hom =
      Prop21StandardSequence.difference M N := by
  apply AddCommGrpCat.hom_ext
  change (equivZMod M N).toAddMonoidHom.comp (quotientMap M N) = psi M N
  exact equivZMod_toAddMonoidHom_comp_quotientMap M N
""", "categorical cokernel equivalence"),
      ("""  map_zero' := by
    ext <;> simp
  map_add' x y := by
    ext <;> simp
""",
       """  map_zero' := by
    apply Prod.ext
    · exact map_zero (ZMod.castHom hM (ZMod M'))
    · exact map_zero (ZMod.castHom hN (ZMod N'))
  map_add' x y := by
    apply Prod.ext
    · exact map_add (ZMod.castHom hM (ZMod M')) x.1 y.1
    · exact map_add (ZMod.castHom hN (ZMod N')) x.2 y.2
""", "residue restriction homomorphism laws"),
      ("""theorem residueRestriction_comp_Phi
    {M N M' N' : ℕ} (hM : M' ∣ M) (hN : N' ∣ N) :
    (residueRestriction hM hN).comp (Phi M N) = Phi M' N' := by
  ext z <;> simp [residueRestriction, Phi]
""",
       """theorem residueRestriction_comp_Phi
    {M N M' N' : ℕ} (hM : M' ∣ M) (hN : N' ∣ N) :
    (residueRestriction hM hN).comp (Phi M N) = Phi M' N' := by
  apply AddMonoidHom.ext
  intro z
  apply Prod.ext <;> simp only [AddMonoidHom.comp_apply, residueRestriction_apply,
    Phi_apply, map_intCast]
""", "residue restriction comparison naturality"),
      ("""theorem gcdRestriction_comp_psi
    {M N M' N' : ℕ} (hM : M' ∣ M) (hN : N' ∣ N) :
    (gcdRestriction hM hN).comp (psi M N) =
      (psi M' N').comp (residueRestriction hM hN) := by
  ext x
  rcases x with ⟨x, y⟩
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  simp [gcdRestriction, residueRestriction, psi]
""",
       """theorem gcdRestriction_comp_psi
    {M N M' N' : ℕ} (hM : M' ∣ M) (hN : N' ∣ N) :
    (gcdRestriction hM hN).comp (psi M N) =
      (psi M' N').comp (residueRestriction hM hN) := by
  apply AddMonoidHom.ext
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  simp only [AddMonoidHom.comp_apply, gcdRestriction_apply, psi_representatives_apply,
    residueRestriction_apply, map_sub, map_intCast]
""", "gcd difference naturality")]

    for old, new, label in pairs:
        text, did = replace_once(text, old, new, f"Mock2 {label}")
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
