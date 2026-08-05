from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(
    text: str, old: str, new: str, label: str, expected: int = 1
) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(
            f"{label}: expected exactly {expected} match(es), found {count}"
        )
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """  unfold denominator
  rw [gammaGL_mul, ← gammaGL_smul δ τ]
  exact UpperHalfPlane.denom_cocycle'
    (gammaGL γ) (gammaGL δ) τ
""",
        """  unfold denominator
  rw [gammaGL_mul, ← gammaGL_smul δ τ]
  simpa [UpperHalfPlane.σ, gammaGL_det_pos] using
    (UpperHalfPlane.denom_cocycle'
      (gammaGL γ) (gammaGL δ) τ)
""",
        "Mock2 reduce the positive-determinant sigma action to the identity",
    )
    m2 = replace_exact(
        m2,
        """local instance : NormedSpace ℂ ℂ :=
  RCLike.innerProductSpace.toNormedSpace ℂ
""",
        """local instance : NormedSpace ℂ ℂ :=
  RCLike.innerProductSpace.toNormedSpace
""",
        "Mock2 select Mathlib's standard complex NormedSpace instance",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  ring
""",
        """  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  simp [firstDerivative]
  <;> ring
""",
        "Mock2 Advanced expose the first derivative in the second derivative coefficient",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [Complex.conj_inv, hConjPow]
        field_simp [hjc]
""",
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [hConjPow]
        field_simp [hjc]
""",
        "FunctionalAnalysis rewrite the conjugate square before cancelling it",
    )
    fa = replace_exact(
        fa,
        """  field_simp [hj, hjc]
  ring
""",
        """  field_simp [hj, hjc]
""",
        "FunctionalAnalysis remove the tactic after field_simp closes lowering algebra",
    )
    fa = replace_exact(
        fa,
        """      _ = 2 * Complex.I * q * c / j * F * u + F * Az := by
        rw [fixedPhaseFactor_holomorphic_direction n γ z]
        simp only [q, c, j, F, Az]
        ring
""",
        """      _ = 2 * Complex.I * q * c / j * F * u + F * Az := by
        rw [fixedPhaseFactor_holomorphic_direction n γ z]
        simp only [q, c, j, F, Az]
""",
        "FunctionalAnalysis remove the tactic after the fixed-phase simplification closes",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
