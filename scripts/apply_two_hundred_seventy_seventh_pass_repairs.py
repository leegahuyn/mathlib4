from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


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
        """  apply ConcreteCategory.hom_ext
  intro e
  simpa [equation613LeftType, equation613RightType] using e.2
""",
        """  apply ConcreteCategory.hom_ext
  intro e
  change AqPresheaf.overlapRestrictionLeft C.openCover e.1 =
    AqPresheaf.overlapRestrictionRight C.openCover e.1
  exact e.2
""",
        "Mock2 use the equalizer subtype property without simplifying it to True",
    )
    m2 = replace_exact(
        m2,
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
        """  have hcompat : F.CompatibleFamily D sf := by
    intro i j
    simpa [D, toMathlibPresheaf] using hsf i j
  obtain ⟨s, hs, huniq⟩ := hF.existsUnique_gluing D sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    simpa [D, toMathlibPresheaf] using hs i
  · intro t ht
    apply huniq t
    intro i
    simpa [D, toMathlibPresheaf] using ht i
""",
        "Mock2 unfold the local OpenCoverData when transporting gluing equations",
    )
    m2 = replace_exact(
        m2,
        "structure ActualProposition20Certificate : Type where\n",
        "structure ActualProposition20Certificate : Type 2 where\n",
        "Mock2 raise the certificate universe to contain categorical limit data",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  intro y hy
  exact (fdHeightMajorant_eq_cuspPowerDensity_add hy).symm
""",
        """  intro y hy
  have hy0 : 0 < y := lt_trans (by norm_num) hy
  exact (fdHeightMajorant_eq_cuspPowerDensity_add hy0).symm
""",
        "Mock2 Advanced derive positivity from membership in Ioi one-half",
    )
    m2a = replace_exact(
        m2a,
        """  simpa only [Function.comp_apply,
    Set.preimage_image_eq _ UpperHalfPlane.coe_injective] using h
""",
        """  simpa only [Function.comp_def,
    Set.preimage_image_eq _ UpperHalfPlane.coe_injective] using h
""",
        "Mock2 Advanced unfold the composed cusp majorant function",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem re_energyForm_self (u : V) :
    (Q.energyForm u u).re =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  rw [energyForm, inner_self_eq_norm_sq]
  norm_num
  exact Q.graph_norm_sq u
""",
        """theorem re_energyForm_self (u : V) :
    (Q.energyForm u u).re =
      ‖Q.base u‖ ^ 2 + ‖Q.raised u‖ ^ 2 + ‖Q.lowered u‖ ^ 2 := by
  rw [energyForm]
  calc
    (⟪Q.graph u, Q.graph u⟫_ℂ).re = ‖Q.graph u‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (Q.graph u)
    _ = _ := Q.graph_norm_sq u
""",
        "FunctionalAnalysis select the graph inner-product instance explicitly",
    )
    fa = replace_exact(
        fa,
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  rw [inner_self_eq_norm_sq]
  norm_num
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)
""",
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  rw [inner_self_eq_norm_sq (𝕜 := ℂ) x]
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)
""",
        "FunctionalAnalysis select the graph-range inner-product instance explicitly",
    )
    fa = replace_exact(
        fa,
        """  intro y
  rw [Q.graphExtension_coe y]
  exact UniformSpace.Completion.norm_coe y
""",
        """  intro y
  rw [Q.graphExtension_coe y]
  rfl
""",
        "FunctionalAnalysis close the normalized completion norm by reflexivity",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
