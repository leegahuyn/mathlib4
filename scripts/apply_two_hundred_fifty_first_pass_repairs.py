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
        """  inverse_is_pointwise_inverse := SmoothGaugeMap.inverse_apply I_G G
  inverse_is_smooth := SmoothGaugeMap.inverse_smooth I_G G
""",
        """  inverse_is_pointwise_inverse := fun U g τ =>
    SmoothGaugeMap.inverse_apply I_G G g τ
  inverse_is_smooth := fun U g =>
    SmoothGaugeMap.inverse_smooth I_G G g
""",
        "Mock2 pass the open set through the inverse certificate fields",
    )
    m2 = replace_exact(
        m2,
        """  restriction_closed := fun V U hVU g hg =>
    GaugeAdmissible.restrict I_G G M D ρ hVU hg
""",
        """  restriction_closed := fun {V U} hVU g hg =>
    GaugeAdmissible.restrict I_G G M D ρ hVU hg
""",
        "Mock2 respect the implicit open sets in restriction closure",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  convert (haff.inv hne).comp_ofReal using 1 <;>
    simp [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
      cuspHorizontalAmbientCurve, one_div, pow_two] <;> ring
""",
        """  convert (haff.inv hne).comp_ofReal using 1
  · funext y
    unfold cuspZeroAmbientCurve cuspHorizontalAmbientCurve
    congr 1
    ring
  · rw [show -((x : ℂ)) - (Y : ℂ) * Complex.I =
        -((x : ℂ) + (Y : ℂ) * Complex.I) by ring]
    simp [cuspFiniteAmbientTangent, cuspHorizontalAmbientCurve,
      one_div, pow_two]
""",
        "Mock2 Advanced discharge the reciprocal function and square identities",
    )
    m2a = replace_exact(
        m2a,
        "rw [hg, mul_assoc, htransition, mul_assoc]",
        "rw [hg, ← mul_assoc, htransition, mul_assoc]",
        "Mock2 Advanced reassociate before applying the representative transition",
        expected=2,
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  rw [physicalExponent_eq_intCast_div_two]
  rw [Complex.ofReal_mul, Complex.ofReal_div]
  ring_nf
""",
        """  rw [physicalExponent_eq_intCast_div_two]
  norm_cast
  dsimp [p]
  field_simp [ne_of_gt z.im_pos]
  ring
""",
        "FunctionalAnalysis reduce the fixed-phase scale derivative to real arithmetic",
    )
    fa = replace_exact(
        fa,
        "SmoothCompactCoreGeometry.RealSmooth.conj",
        "RealSmooth.conj",
        "FunctionalAnalysis use the local real-smooth conjugation namespace",
        expected=5,
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
