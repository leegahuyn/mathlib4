from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """def toMathlibPresheaf (F : PresheafLike X) :
    TopCat.Presheaf (Type v) (TopCat.of X) where
  obj U := F.Section U.unop
  map f := F.res f.unop.le
  map_id U := by
    funext s
    exact F.res_id U.unop s
  map_comp f g := by
    funext s
    exact (F.res_comp g.unop.le f.unop.le s).symm
""",
        """def toMathlibPresheaf (F : PresheafLike X) :
    TopCat.Presheaf (Type v) (TopCat.of X) where
  obj U := F.Section U.unop
  map f := ↾(F.res f.unop.le)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro s
    exact F.res_id U.unop s
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (F.res_comp g.unop.le f.unop.le s).symm
""",
        "Mock2 construct the Mathlib presheaf maps in the Type category",
    )
    m2 = replace_exact(
        m2,
        """@[simp] theorem toMathlibPresheaf_map_apply (F : PresheafLike X)
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (f : U ⟶ V)
    (s : F.Section U.unop) :
    (toMathlibPresheaf F).map f s = F.res f.unop.le s := rfl
""",
        """@[simp] theorem toMathlibPresheaf_map_apply (F : PresheafLike X)
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (f : U ⟶ V)
    (s : F.Section U.unop) :
    (toMathlibPresheaf F).map f s = F.res f.unop.le s := by
  rfl
""",
        "Mock2 expose evaluation of the Type-valued restriction morphism",
    )
    m2 = replace_exact(
        m2,
        """  have hcompat : F.CompatibleFamily D sf := by
    intro i j
    exact hsf i j
  obtain ⟨s, hs, huniq⟩ := hF.existsUnique_gluing D sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    change F.res (le_iSup U i) s = sf i
    exact hs i
  · intro t ht
    apply huniq t
    intro i
    change F.res (le_iSup U i) t = sf i
    exact ht i
""",
        """  have hcompat : F.CompatibleFamily D sf := by
    intro i j
    simpa [toMathlibPresheaf] using hsf i j
  obtain ⟨s, hs, huniq⟩ := hF.existsUnique_gluing D sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    simpa [toMathlibPresheaf] using hs i
  · intro t ht
    apply huniq t
    intro i
    simpa [toMathlibPresheaf] using ht i
""",
        "Mock2 transport the custom gluing equations through Type morphisms",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
