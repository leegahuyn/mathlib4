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
        "def Bq : QGaugePresheaf.{0, v} Opens :=\n",
        "def Bq : QGaugePresheaf Opens :=\n",
        "Mock2 restore the public boundary-presheaf universe",
    )
    m2 = replace_once(
        m2,
        """  have hcompat :
      (QGaugePresheaf.toPresheafLike P).CompatibleFamily C sf := by
    intro i j
    simpa only [toMathlibPresheaf_map_apply] using hsf i j
  obtain ⟨s, hs, huniq⟩ := hP.existsUnique_gluing C sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    simpa only [toMathlibPresheaf_map_apply] using hs i
  · intro t ht
    apply huniq t
    intro i
    simpa only [toMathlibPresheaf_map_apply] using ht i
""",
        """  have hcompat :
      (QGaugePresheaf.toPresheafLike P).CompatibleFamily C sf := by
    intro i j
    change
      (toMathlibPresheaf P).map ((U i).infLELeft (U j)).op (sf i) =
        (toMathlibPresheaf P).map ((U i).infLERight (U j)).op (sf j)
    exact hsf i j
  obtain ⟨s, hs, huniq⟩ := hP.existsUnique_gluing C sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    change P.res (le_iSup U i) s = sf i
    exact hs i
  · intro t ht
    apply huniq t
    intro i
    change (toMathlibPresheaf P).map (le_iSup U i).op t = sf i
    exact ht i
""",
        "Mock2 align lightweight and Mathlib gluing goals explicitly",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_once(
        m2a,
        "have hx : (1 / 2 : ℝ) ∈ Ioc 0 1 := by norm_num",
        "have hx : (2 : ℝ)⁻¹ ∈ Ioc 0 1 := by norm_num",
        "Mock2 Advanced normalize the interval midpoint as an inverse",
    )
    m2a = replace_once(
        m2a,
        """theorem eq_average_of_eq_of_eq
    {R : Type*} [LinearOrderedField R]""",
        """theorem eq_average_of_eq_of_eq
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]""",
        "Mock2 Advanced replace removed ordered-field class in average leaf",
    )
    m2a = replace_once(
        m2a,
        """theorem average_factorization_identity
    {R : Type*} [LinearOrderedField R]""",
        """theorem average_factorization_identity
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]""",
        "Mock2 Advanced replace removed ordered-field class in factorization",
    )
    m2a = replace_once(
        m2a,
        """theorem energy_add_boundary_eq_rhs_iff
    {R : Type*} [LinearOrderedRing R]""",
        """theorem energy_add_boundary_eq_rhs_iff
    {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]""",
        "Mock2 Advanced replace removed ordered-ring class in sign equivalence",
    )
    m2a = replace_once(
        m2a,
        """theorem energy_eq_rhs_sub_boundary
    {R : Type*} [LinearOrderedRing R]""",
        """theorem energy_eq_rhs_sub_boundary
    {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]""",
        "Mock2 Advanced replace removed ordered-ring class in boundary move",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_once(
        fa,
        """  factor_cocycle := by
    intro γ δ z
    have hexp : paperOrbitExponent n = -(1 - 4 * n) := by
      simp [paperOrbitExponent, paperDisplayedExponentIndex]
      ring
    simpa only [hexp] using
      (inverseEtaHalfOrbitMultiplier Γ n).factor_cocycle γ δ z
""",
        """  factor_cocycle := by
    intro γ δ z
    have hexp : -(-paperOrbitExponent n) = -(1 - 4 * n) := by
      simp [paperOrbitExponent, paperDisplayedExponentIndex]
      ring
    simpa only [hexp] using
      (inverseEtaHalfOrbitMultiplier Γ n).factor_cocycle γ δ z
""",
        "FunctionalAnalysis transport the actual negated orbit exponent in the cocycle",
    )
    fa = replace_once(
        fa,
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
        """  change
    (inverseEtaHalfOrbitMultiplier Γ n).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor γ z ^
          (-(-paperOrbitExponent n)) = _
  have hexp : -(-paperOrbitExponent n) = -(1 - 4 * n) := by
    simp [paperOrbitExponent, paperDisplayedExponentIndex]
    ring
  rw [hexp]
  exact inverseEtaHalfOrbitMultiplier_factor Γ n γ z
""",
        "FunctionalAnalysis expose the actual paper-orbit factor exponent",
    )
    fa = replace_once(
        fa,
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
        """  change
    (inverseEtaHalfOrbitMultiplier Γ (n + 1)).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ (n + 1)).sqrtFactor γ z ^
          (-(-paperOrbitExponent (n + 1))) =
      ((inverseEtaHalfOrbitMultiplier Γ n).nu γ *
        (inverseEtaHalfOrbitMultiplier Γ n).sqrtFactor γ z ^
          (-(-paperOrbitExponent n))) *
        UpperHalfPlane.denom
          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) z ^ (2 : ℕ)
  have hexp_succ : -(-paperOrbitExponent (n + 1)) = -(1 - 4 * (n + 1)) := by
    simp [paperOrbitExponent, paperDisplayedExponentIndex]
    ring
  have hexp : -(-paperOrbitExponent n) = -(1 - 4 * n) := by
    simp [paperOrbitExponent, paperDisplayedExponentIndex]
    ring
  rw [hexp_succ, hexp]
  exact inverseEtaHalfOrbitMultiplier_factor_add_one Γ n γ z
""",
        "FunctionalAnalysis expose both actual successor orbit exponents",
    )
    fa = replace_once(
        fa,
        """      exact ((Complex.differentiableAt_sqrt
        (Complex.mem_slitPlane_iff.mpr (Or.inr hIm))).comp w hDenom).
          differentiableWithinAt
""",
        """      exact ((Complex.differentiableAt_sqrt
        (Complex.mem_slitPlane_iff.mpr (Or.inr hIm))).comp w hDenom).differentiableWithinAt
""",
        "FunctionalAnalysis repair differentiableWithinAt field notation",
    )
    fa = replace_once(
        fa,
        """      (hDifferentiable.analyticOnNhd
        UpperHalfPlane.isOpen_upperHalfPlaneSet).restrictScalars.
          contDiffOn_of_completeSpace
""",
        """      (hDifferentiable.analyticOnNhd
        UpperHalfPlane.isOpen_upperHalfPlaneSet).restrictScalars.contDiffOn_of_completeSpace
""",
        "FunctionalAnalysis repair contDiff field notation",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
