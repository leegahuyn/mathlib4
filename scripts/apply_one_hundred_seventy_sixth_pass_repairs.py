from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly one match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_once(
        m2,
        "def Bq : QGaugePresheaf Opens :=\n",
        "def Bq : QGaugePresheaf.{0, v} Opens :=\n",
        "Mock2 lift Bq fibre universe",
    )
    m2 = replace_once(
        m2,
        "  map f := ConcreteCategory.ofHom (P.res f.unop.le)\n",
        "  map f := TypeCat.ofHom (P.res f.unop.le)\n",
        "Mock2 use TypeCat presheaf morphisms",
    )
    m2 = replace_once(
        m2,
        """    (toMathlibPresheaf P).map f s = P.res f.unop.le s := by
  change ConcreteCategory.hom
      (ConcreteCategory.ofHom (P.res f.unop.le)) s = _
  rw [ConcreteCategory.hom_ofHom]
""",
        """    (toMathlibPresheaf P).map f s = P.res f.unop.le s :=
  rfl
""",
        "Mock2 simplify TypeCat map evaluation",
    )
    m2 = replace_once(
        m2,
        "  app U := ConcreteCategory.ofHom (φ.app U.unop)\n",
        "  app U := TypeCat.ofHom (φ.app U.unop)\n",
        "Mock2 use TypeCat natural transformation components",
    )
    m2 = replace_once(
        m2,
        """    (toMathlibNatTrans φ).app U s = φ.app U.unop s := by
  change ConcreteCategory.hom
      (ConcreteCategory.ofHom (φ.app U.unop)) s = _
  rw [ConcreteCategory.hom_ofHom]
""",
        """    (toMathlibNatTrans φ).app U s = φ.app U.unop s :=
  rfl
""",
        "Mock2 simplify TypeCat natural transformation evaluation",
    )
    m2 = replace_once(
        m2,
        """abbrev ActualSheafCategory :=
  TopCat.Sheaf (Type 0) (TopCat.of RadiusBase)
""",
        """abbrev ActualSheafCategory :=
  TopCat.Sheaf (Type v) (TopCat.of RadiusBase)
""",
        "Mock2 restore actual sheaf universe",
    )
    m2 = replace_once(
        m2,
        "def mathlibAq : ActualSheafCategory :=\n",
        "def mathlibAq : ActualSheafCategory.{v} :=\n",
        "Mock2 pin mathlibAq universe",
    )
    m2 = replace_once(
        m2,
        "def mathlibBq : ActualSheafCategory :=\n",
        "def mathlibBq : ActualSheafCategory.{v} :=\n",
        "Mock2 pin mathlibBq universe",
    )
    m2 = replace_once(
        m2,
        "def mathlibEqSheaf : ActualSheafCategory :=\n",
        "def mathlibEqSheaf : ActualSheafCategory.{v} :=\n",
        "Mock2 pin mathlibEqSheaf universe",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    replacements = (
        (
            "(productUnfolding T hT).geometric.set n",
            "(productUnfolding.{0} T hT).geometric.set n",
            "Mock2 Advanced pin geometric unfolding universe",
        ),
        (
            "((productUnfolding T hT).spectral k)",
            "((productUnfolding.{0} T hT).spectral k)",
            "Mock2 Advanced pin spectral unfolding universe",
        ),
        (
            "(productUnfolding T hT).finiteIdentity n m",
            "(productUnfolding.{0} T hT).finiteIdentity n m",
            "Mock2 Advanced pin finite identity universe",
        ),
        (
            "MassUnfolding.product_unfolding_to_mass (productUnfolding T hT) m",
            "MassUnfolding.product_unfolding_to_mass (productUnfolding.{0} T hT) m",
            "Mock2 Advanced pin limit bridge universe",
        ),
    )
    for old, new, label in replacements:
        m2a = replace_once(m2a, old, new, label)
    m2a = replace_once(
        m2a,
        """  rw [productKernel, unitIntervalDensity, Set.indicator_of_mem hx,
    stageTest, Set.indicator_of_mem ht, one_mul]
  exact
    KuznetsovInterface.fourierPositiveSmoothTentFunction_pos_zero T hT
""",
        """  simpa [productKernel, unitIntervalDensity, hx, stageTest, ht] using
    KuznetsovInterface.fourierPositiveSmoothTentFunction_pos_zero T hT
""",
        "Mock2 Advanced simplify product kernel center positivity",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_once(
        fa,
        """  factor_cocycle := by
    intro γ δ z
    have h := (inverseEtaHalfOrbitMultiplier Γ n).factor_cocycle γ δ z
    convert h using 1 <;> ring
""",
        """  factor_cocycle := by
    intro γ δ z
    have hexp : paperOrbitExponent n = -(1 - 4 * n) := by
      simp [paperOrbitExponent, paperDisplayedExponentIndex]
      ring
    simpa only [hexp] using
      (inverseEtaHalfOrbitMultiplier Γ n).factor_cocycle γ δ z
""",
        "FunctionalAnalysis transport orbit cocycle by exact exponent equality",
    )
    fa = replace_once(
        fa,
        """  change
    (inverseEtaHalfOrbitMultiplier Γ n).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor γ z ^
          (-(-paperOrbitExponent n)) = _
  have h := inverseEtaHalfOrbitMultiplier_factor Γ n γ z
  unfold HalfIntegralMultiplier.factor at h
  convert h using 1 <;> ring
""",
        """  change
    (inverseEtaHalfOrbitMultiplier Γ n).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor γ z ^
          paperOrbitExponent n = _
  have hexp : paperOrbitExponent n = -(1 - 4 * n) := by
    simp [paperOrbitExponent, paperDisplayedExponentIndex]
    ring
  rw [hexp]
  exact inverseEtaHalfOrbitMultiplier_factor Γ n γ z
""",
        "FunctionalAnalysis transport orbit factor by exact exponent equality",
    )
    fa = replace_once(
        fa,
        """  change
    (inverseEtaHalfOrbitMultiplier Γ (n + 1)).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ (n + 1)).sqrtFactor γ z ^
          (-(-paperOrbitExponent (n + 1))) =
      ((inverseEtaHalfOrbitMultiplier Γ n).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor γ z ^
          (-(-paperOrbitExponent n))) *
        UpperHalfPlane.denom
          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) z ^ (2 : ℕ)
  have h := inverseEtaHalfOrbitMultiplier_factor_add_one Γ n γ z
  unfold HalfIntegralMultiplier.factor at h
  convert h using 1 <;> ring
""",
        """  change
    (inverseEtaHalfOrbitMultiplier Γ (n + 1)).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ (n + 1)).sqrtFactor γ z ^
          paperOrbitExponent (n + 1) =
      ((inverseEtaHalfOrbitMultiplier Γ n).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor γ z ^
          paperOrbitExponent n) *
        UpperHalfPlane.denom
          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) z ^ (2 : ℕ)
  have hexp_succ : paperOrbitExponent (n + 1) = -(1 - 4 * (n + 1)) := by
    simp [paperOrbitExponent, paperDisplayedExponentIndex]
    ring
  have hexp : paperOrbitExponent n = -(1 - 4 * n) := by
    simp [paperOrbitExponent, paperDisplayedExponentIndex]
    ring
  rw [hexp_succ, hexp]
  exact inverseEtaHalfOrbitMultiplier_factor_add_one Γ n γ z
""",
        "FunctionalAnalysis transport successor factor by exact exponent equalities",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
