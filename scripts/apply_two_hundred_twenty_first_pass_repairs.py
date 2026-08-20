from __future__ import annotations

from pathlib import Path

import apply_two_hundred_twenty_second_pass_repairs as pass222

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
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
        """theorem lineSmul_contMDiff {B : HalfWeightBranch}
    (M : MultiplierSystem B) (γ : Gamma2) :
    ContMDiff ((𝓘(ℂ)).prod (𝓘(ℂ))) ((𝓘(ℂ)).prod (𝓘(ℂ))) ∞
      (lineSmul M γ) := by
  simpa [lineSmul] using
    (((deckAction_contMDiff γ).comp contMDiff_fst).prodMk
      (((M.automorphyFactor_contMDiff γ).comp contMDiff_fst).mul
        contMDiff_snd))
""",
        """theorem lineSmul_contMDiff {B : HalfWeightBranch}
    (M : MultiplierSystem B) (γ : Gamma2) :
    ContMDiff ((𝓘(ℂ)).prod (𝓘(ℂ))) ((𝓘(ℂ)).prod (𝓘(ℂ))) ∞
      (lineSmul M γ) := by
  change ContMDiff ((𝓘(ℂ)).prod (𝓘(ℂ)))
    ((𝓘(ℂ)).prod (𝓘(ℂ))) ∞
      (fun p : H × ℂ =>
        (γ • p.1, (M.automorphyFactor γ p.1 : ℂ) * p.2))
  exact (((deckAction_contMDiff γ).comp contMDiff_fst).prodMk
    (((M.automorphyFactor_contMDiff γ).comp contMDiff_fst).mul
      contMDiff_snd))
""",
        "Mock2 expose the line action before the product smoothness proof",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularUnitCircleCurve (t : ℝ) :
    HasDerivAt modularUnitCircleCurve (modularUnitCircleTangent t) t := by
  simpa [modularUnitCircleCurve, modularUnitCircleTangent] using
    (((Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp
      (t : ℂ) (hasDerivAt_mul_const Complex.I)).comp_ofReal)
""",
        """theorem hasDerivAt_modularUnitCircleCurve (t : ℝ) :
    HasDerivAt modularUnitCircleCurve (modularUnitCircleTangent t) t := by
  change HasDerivAt
    (fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
    (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t
  exact (((Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp
    (t : ℂ) (hasDerivAt_mul_const Complex.I)).comp_ofReal)
""",
        "Mock2 Advanced expose the unit-circle curve in its derivative theorem",
    )
    m2a = replace_exact(
        m2a,
        """theorem contDiff_modularUnitCircleCurve :
    ContDiff ℝ (↑(⊤ : ℕ∞)) modularUnitCircleCurve := by
  unfold modularUnitCircleCurve
  fun_prop
""",
        """theorem contDiff_modularUnitCircleCurve :
    ContDiff ℝ (↑(⊤ : ℕ∞)) modularUnitCircleCurve := by
  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
  exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp
""",
        "Mock2 Advanced prove unit-circle smoothness compositionally",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """/-- The elementary algebra at the end of the lowering covariance proof. -/
set_option maxHeartbeats 800000 in
private theorem lower_covariance_algebra
""",
        """/- The elementary algebra at the end of the lowering covariance proof. -/
set_option maxHeartbeats 3000000 in
private theorem lower_covariance_algebra
""",
        "FunctionalAnalysis fix the scoped heartbeat command and raise its local budget",
    )
    FA.write_text(fa, encoding="utf-8")
    return pass222.main()


if __name__ == "__main__":
    raise SystemExit(main())
