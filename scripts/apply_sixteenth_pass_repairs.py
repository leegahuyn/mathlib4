from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Mock2.lean")


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


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            "def zeroObject : Ab := 0",
            "def zeroObject : Ab := AddCommGrpCat.of (ZMod 1)",
            "Mock2 explicit trivial additive group object",
        ),
        (
            """  simp only [AddMonoidHom.comp_apply, gcdRestriction_apply, psi_representatives_apply,
    residueRestriction_apply, map_sub, map_intCast]
""",
            """  simp only [AddMonoidHom.comp_apply, gcdRestriction, psi_representatives_apply,
    residueRestriction_apply, map_intCast]
""",
            "Mock2 unfold gcd restriction on integer representatives",
        ),
        (
            """  comm₁₂ := by simp [Prop21StandardSequence.zeroToIntersection]
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    simpa [Prop21StandardSequence.intersectionInclusion] using
      (intersectionRestriction_comp_inclusion hM hN)
""",
            """  comm₁₂ := by
    simp only [Category.id_comp, Category.zero_comp]
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    change (intersectionIdealIncl M' N').comp
      (intersectionRestriction hM hN) = intersectionIdealIncl M N
    exact intersectionRestriction_comp_inclusion hM hN
""",
            "Mock2 left endpoint short-complex squares",
        ),
        (
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    simpa [Prop21StandardSequence.intersectionInclusion] using
      (intersectionRestriction_comp_inclusion hM hN)
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    simpa [Prop21StandardSequence.comparison] using
      (residueRestriction_comp_Phi hM hN).symm
""",
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    change (intersectionIdealIncl M' N').comp
      (intersectionRestriction hM hN) = intersectionIdealIncl M N
    exact intersectionRestriction_comp_inclusion hM hN
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    change Phi M' N' = (residueRestriction hM hN).comp (Phi M N)
    exact (residueRestriction_comp_Phi hM hN).symm
""",
            "Mock2 integer short-complex squares",
        ),
        (
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    simpa [Prop21StandardSequence.comparison] using
      (residueRestriction_comp_Phi hM hN).symm
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    simpa [Prop21StandardSequence.difference] using
      (gcdRestriction_comp_psi hM hN).symm
""",
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    change Phi M' N' = (residueRestriction hM hN).comp (Phi M N)
    exact (residueRestriction_comp_Phi hM hN).symm
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    change (psi M' N').comp (residueRestriction hM hN) =
      (gcdRestriction hM hN).comp (psi M N)
    exact (gcdRestriction_comp_psi hM hN).symm
""",
            "Mock2 residue-product short-complex squares",
        ),
        (
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    simpa [Prop21StandardSequence.difference] using
      (gcdRestriction_comp_psi hM hN).symm
  comm₂₃ := by simp [Prop21StandardSequence.gcdToZero]
""",
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    change (psi M' N').comp (residueRestriction hM hN) =
      (gcdRestriction hM hN).comp (psi M N)
    exact (gcdRestriction_comp_psi hM hN).symm
  comm₂₃ := by
    simp only [Category.comp_zero, Category.zero_comp, Category.comp_id]
""",
            "Mock2 right endpoint short-complex squares",
        ),
        (
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    simpa [PhiCokernel.atResidueProduct,
      Prop21StandardSequence.comparison] using
      (residueRestriction_comp_Phi hM hN).symm
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    simpa [PhiCokernel.atResidueProduct,
      PhiCokernel.quotientMorphism] using
      (cokernelMap_comp_quotientMap hM hN).symm
""",
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    change Phi M' N' = (residueRestriction hM hN).comp (Phi M N)
    exact (residueRestriction_comp_Phi hM hN).symm
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    change (PhiCokernel.quotientMap M' N').comp
      (residueRestriction hM hN) =
        (cokernelMap hM hN).comp (PhiCokernel.quotientMap M N)
    exact (cokernelMap_comp_quotientMap hM hN).symm
""",
            "Mock2 actual cokernel residue-product squares",
        ),
        (
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    simpa [PhiCokernel.rightEndpoint,
      PhiCokernel.quotientMorphism] using
      (cokernelMap_comp_quotientMap hM hN).symm
  comm₂₃ := by simp [PhiCokernel.rightEndpoint, PhiCokernel.toZero]
""",
            """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    change (PhiCokernel.quotientMap M' N').comp
      (residueRestriction hM hN) =
        (cokernelMap hM hN).comp (PhiCokernel.quotientMap M N)
    exact (cokernelMap_comp_quotientMap hM hN).symm
  comm₂₃ := by
    simp only [Category.comp_zero, Category.zero_comp, Category.comp_id]
""",
            "Mock2 actual cokernel right-endpoint squares",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
