from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


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
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  have hγ' :
      (((γ.1 : IntegralSpecialLinear) : GL (Fin 2) ℝ) • x) = y := by
    simpa only [ModularGroup.sl_moeb] using hγ
""",
        """  have hγ' :
      (((γ.1 : IntegralSpecialLinear) : GL (Fin 2) ℝ) • x) = y := by
    change (γ.1 : IntegralSpecialLinear) • x = y at hγ
    simpa only [ModularGroup.sl_moeb] using hγ
""",
        "Mock2 Advanced expose the subgroup action before the real GL coercion",
    )
    m2a = replace_exact(
        m2a,
        """  have hcancel := congrArg
    (fun z : UpperHalfPlane => (repMatrix r)⁻¹ • z) hfundamental
  simpa only [← mul_smul, inv_mul, one_smul] using hcancel
""",
        """  have hcancel := congrArg
    (fun z : UpperHalfPlane => (repMatrix r)⁻¹ • z) hfundamental
  simpa [← mul_smul] using hcancel
""",
        "Mock2 Advanced cancel the representative action by simplification",
    )
    m2a = replace_exact(
        m2a,
        """theorem repMatrix_stInv_im (τ : UpperHalfPlane) :
    (repMatrix .stInv • τ).im = cuspHeight .one τ := by
  rw [repMatrix_stInv]
  change ((ModularGroup.S * ModularGroup.T⁻¹) • τ).im =
    (((ModularGroup.T * ModularGroup.S)⁻¹) • τ).im
  rw [mul_inv_rev, ModularGroup.S_inv, mul_smul,
    ModularGroup.SL_neg_smul]
""",
        """theorem repMatrix_stInv_im (τ : UpperHalfPlane) :
    (repMatrix .stInv • τ).im = cuspHeight .one τ := by
  rw [repMatrix_stInv]
  change ((ModularGroup.S * ModularGroup.T⁻¹) • τ).im =
    (((ModularGroup.T * ModularGroup.S)⁻¹) • τ).im
  simp only [mul_inv_rev, ModularGroup.S_inv, mul_smul,
    ModularGroup.SL_neg_smul]
""",
        "Mock2 Advanced normalize every occurrence in the stInv height identity",
    )
    m2a = replace_exact(
        m2a,
        """theorem repMatrix_tstInv_im (τ : UpperHalfPlane) :
    (repMatrix .tstInv • τ).im = cuspHeight .one τ := by
  rw [repMatrix_tstInv, ← mul_assoc, mul_smul,
    ModularGroup.im_T_smul]
  simpa only [repMatrix_stInv, mul_smul] using repMatrix_stInv_im τ
""",
        """theorem repMatrix_tstInv_im (τ : UpperHalfPlane) :
    (repMatrix .tstInv • τ).im = cuspHeight .one τ := by
  rw [repMatrix_tstInv, ← mul_assoc, mul_smul,
    ModularGroup.im_T_smul]
  simpa only [repMatrix_stInv] using repMatrix_stInv_im τ
""",
        "Mock2 Advanced reuse the stInv height identity without over-expanding actions",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
