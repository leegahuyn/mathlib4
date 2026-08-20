from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  funext s
  change (liftedResIn D K A).app U.unop s.1 =
""",
        """  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CategoryTheory.ConcreteCategory.ext_apply
  intro s
  change (liftedResIn D K A).app U.unop s.1 =
""",
        "Mock2 compare the equalizer condition pointwise in TypeCat",
    )
    m2 = replace_exact(
        m2,
        "simpa only [TopCat.Sheaf.comp_app, Function.comp_apply] using h",
        "simpa only [CategoryTheory.comp_apply] using h",
        "Mock2 evaluate categorical composites pointwise",
        expected=2,
    )
    m2 = replace_exact(
        m2,
        """  ObjectProperty.homMk
    { app := fun U s =>
        ⟨S.ι.hom.app U s, fork_condition_apply D K A S U s⟩
      naturality := by
        intro U W f
        funext s
        apply Subtype.ext
        simpa only [Function.comp_apply] using
          congrFun (S.ι.hom.naturality f) s }
""",
        """  ObjectProperty.homMk
    { app := fun U => TypeCat.ofHom fun s =>
        ⟨S.ι.hom.app U s, fork_condition_apply D K A S U s⟩
      naturality := by
        intro U W f
        apply CategoryTheory.ConcreteCategory.ext_apply
        intro s
        apply Subtype.ext
        simpa only [CategoryTheory.comp_apply] using
          CategoryTheory.ConcreteCategory.congr_hom
            (S.ι.hom.naturality f) s }
""",
        "Mock2 bundle the subtype lift as TypeCat morphisms",
    )
    m2 = replace_exact(
        m2,
        """  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  funext s
  rfl
""",
        """  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CategoryTheory.ConcreteCategory.ext_apply
  intro s
  rfl
""",
        "Mock2 prove the subtype factorization pointwise",
    )
    m2 = replace_exact(
        m2,
        """  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  funext s
  apply Subtype.ext
""",
        """  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CategoryTheory.ConcreteCategory.ext_apply
  intro s
  apply Subtype.ext
""",
        "Mock2 prove uniqueness pointwise in TypeCat",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  rw [hstar, ← Complex.exp_add]
  congr 1
  simp only [map_mul, ← Complex.ofReal_intCast, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring
""",
        """  have harg :
      star ((n : ℂ) * Real.pi * Complex.I * (x : ℂ)) =
        -((n : ℂ) * Real.pi * Complex.I * (x : ℂ)) := by
    change Complex.conj
      ((n : ℂ) * Real.pi * Complex.I * (x : ℂ)) =
        -((n : ℂ) * Real.pi * Complex.I * (x : ℂ))
    simp only [map_mul, ← Complex.ofReal_intCast, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring
  rw [hstar, harg, ← Complex.exp_add]
  congr 1
  ring
""",
        "Mock2 Advanced normalize the conjugated Fourier exponent",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """    rw [inverseEtaPaperOrbitFactor_eq_eta]
    simp only [explicitFactor, inverseEtaPaperOrbitDenom, g])
""",
        """    rw [inverseEtaPaperOrbitFactor_eq_eta]
    simp only [explicitFactor, inverseEtaPaperOrbitDenom, g,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw])
""",
        "FunctionalAnalysis identify the eta factor after unfolding",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
