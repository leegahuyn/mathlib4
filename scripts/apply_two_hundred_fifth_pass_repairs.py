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
        """local attribute [-instance]
  instNormedSpaceComplex_primalitySheafVerification
""",
        """attribute [-instance]
  instNormedSpaceComplex_primalitySheafVerification
""",
        "Mock2 remove the project-specific complex NormedSpace instance attribute",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem repMatrix_tstInv_im (τ : UpperHalfPlane) :
    (repMatrix .tstInv • τ).im = cuspHeight .one τ := by
  rw [repMatrix_tstInv, ← mul_assoc, mul_smul,
    ModularGroup.im_T_smul]
  simpa only [repMatrix_stInv] using repMatrix_stInv_im τ
""",
        """theorem repMatrix_tstInv_im (τ : UpperHalfPlane) :
    (repMatrix .tstInv • τ).im = cuspHeight .one τ := by
  rw [repMatrix_tstInv, mul_assoc, mul_smul,
    ModularGroup.im_T_smul]
  simpa only [repMatrix_stInv] using repMatrix_stInv_im τ
""",
        "Mock2 Advanced reassociate tstInv in the direction used by the action",
    )
    m2a = replace_exact(
        m2a,
        """  rw [Complex.normSq_apply]
  nlinarith
""",
        """  rw [Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith [hprod]
""",
        "Mock2 Advanced expose upper-half-plane coordinates in the norm upper bound",
    )
    m2a = replace_exact(
        m2a,
        """theorem im_sq_le_normSq (z : UpperHalfPlane) :
    z.im ^ 2 ≤ Complex.normSq (z : ℂ) := by
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg z.re]
""",
        """theorem im_sq_le_normSq (z : UpperHalfPlane) :
    z.im ^ 2 ≤ Complex.normSq (z : ℂ) := by
  rw [Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith [sq_nonneg z.re]
""",
        "Mock2 Advanced expose upper-half-plane coordinates in the norm lower bound",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [hConjPow]
        field_simp [hjc]
""",
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [← hConjPow]
        field_simp [hjc]
""",
        "FunctionalAnalysis rewrite the outer conjugate square toward cancellation",
    )
    fa = replace_exact(
        fa,
        """noncomputable instance (n : ℤ) :
    Coe (InverseEtaFixedPhaseCore n) SmoothQuotientCompactFunction :=
  ⟨toSmoothQuotientCompactFunction⟩
""",
        """noncomputable instance (n : ℤ) :
    CoeOut (InverseEtaFixedPhaseCore n) SmoothQuotientCompactFunction :=
  ⟨toSmoothQuotientCompactFunction⟩
""",
        "FunctionalAnalysis use an output-directed coercion for the indexed stable core",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
