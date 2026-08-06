from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """/-- Value of a `𝔤`-valued one-form in the complex chart of `ℍ`. -/
abbrev OneFormValue := ℂ →L[ℂ] GaugeLieAlgebra I_G G

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        """/-- Value of a `𝔤`-valued one-form in the complex chart of `ℍ`. -/
abbrev OneFormValue := ℂ →L[ℂ] GaugeLieAlgebra I_G G

noncomputable local instance oneFormValueNormedAddCommGroup :
    NormedAddCommGroup (OneFormValue I_G G) := by
  change NormedAddCommGroup (ℂ →L[ℂ] E_G)
  infer_instance

noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] E_G)
  infer_instance

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        "Mock2 restore only the canonical one-form norm structures",
    )
    m2 = replace_exact(
        m2,
        """    (s : (strictEqualityTwistedOneFormPresheaf I_G G M).
      CoverSectionProduct C) : Prop :=
""",
        """    (s : (strictEqualityTwistedOneFormPresheaf I_G G M).CoverSectionProduct C) : Prop :=
""",
        "Mock2 keep the strict overlap section projection on one line",
    )
    m2 = replace_exact(
        m2,
        """    (s : (strictEqualityTwistedOneFormPresheaf I_G G M).
      CoverSectionProduct C) :
""",
        """    (s : (strictEqualityTwistedOneFormPresheaf I_G G M).CoverSectionProduct C) :
""",
        "Mock2 keep the literal-overlap section projection on one line",
    )
    m2 = replace_exact(
        m2,
        """      (s : (strictEqualityTwistedOneFormPresheaf I_G G M).
        CoverSectionProduct C),
""",
        """      (s : (strictEqualityTwistedOneFormPresheaf I_G G M).CoverSectionProduct C),
""",
        "Mock2 keep the certificate overlap projection on one line",
    )
    M2.write_text(m2, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """    have hcoeff := weighted_inverse_height_coefficient a hw
    linear_combination -(star (u w)) * hcoeff
""",
        """    have hcoeff := weighted_inverse_height_coefficient a hw
    rw [← hcoeff]
    ring
""",
        "FunctionalAnalysis rewrite the lowering coefficient before ring normalization",
    )
    fa = replace_exact(
        fa,
        """  have him : (UpperHalfPlane.ofComplex w).im = w.im := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
""",
        """  have him : (UpperHalfPlane.ofComplex w).im = w.im := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    rfl
""",
        "FunctionalAnalysis close the upper-half-plane imaginary projection definitionally",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
