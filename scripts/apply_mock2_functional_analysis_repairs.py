from __future__ import annotations

import re
from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False
    if "λ" in text:
        text = text.replace("λ", "lam")
        changed = True
        print("renamed reserved lambda identifier")

    for name in ["dualPairing", "coreRatioNorm", "antiDualPairing",
        "linearBochnerPairing", "antiBochnerPairing", "realifiedFunctionalLinear",
        "realifiedFunctional", "realifiedFormLinear", "realifiedForm", "rieszMassForm",
        "fredholmDefectKernelComplementRestriction", "kernelComplementRestriction", "factor"]:
        text2, n = re.subn(rf"(?m)^def {re.escape(name)}\b",
            f"noncomputable def {name}", text, count=1)
        if n:
            text = text2
            changed = True
            print(f"noncomputable {name}")

    text2, n = re.subn(r"(?<![A-Za-z0-9_.])Tendsto\b", "Filter.Tendsto", text)
    if n:
        text, changed = text2, True
    text2, n = re.subn(r"(?<![A-Za-z0-9_.])atTop\b", "Filter.atTop", text)
    if n:
        text, changed = text2, True

    text = text.replace(
"""theorem innerSLFlip_pairing [InnerProductSpace ℂ E] (u v : E) :
""",
"""omit [NormedSpace ℂ E] in
theorem innerSLFlip_pairing [InnerProductSpace ℂ E] (u v : E) :
""")
    text = text.replace(
"""theorem weakLinearSolution_norm_le (A : E ≃L[ℂ] StrongDual ℂ E)
    (f : StrongDual ℂ E) :
    ‖weakLinearSolution A f‖ ≤ ‖A.symm‖ * ‖f‖ :=
  A.symm.le_opNorm f
""",
"""theorem weakLinearSolution_norm_le (A : E ≃L[ℂ] StrongDual ℂ E)
    (f : StrongDual ℂ E) :
    ‖weakLinearSolution A f‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖f‖ :=
  A.symm.toContinuousLinearMap.le_opNorm f
""")
    text = text.replace(
"""  simpa only [smul_eq_mul] using
    (MeasureTheory.integral_smul c (linearTestIntegrand ρ T v))
""",
"""  change (∫ x, c * linearTestIntegrand ρ T v x ∂μ) =
    c * ∫ x, linearTestIntegrand ρ T v x ∂μ
  exact MeasureTheory.integral_smul c (linearTestIntegrand ρ T v)
""")
    text = text.replace(
"""  simpa only [smul_eq_mul] using
    (MeasureTheory.integral_smul ((starRingEnd ℂ) c)
      (antiTestIntegrand ρ T v))
""",
"""  change (∫ x, (starRingEnd ℂ) c * antiTestIntegrand ρ T v x ∂μ) =
    (starRingEnd ℂ) c * ∫ x, antiTestIntegrand ρ T v x ∂μ
  exact MeasureTheory.integral_smul ((starRingEnd ℂ) c)
    (antiTestIntegrand ρ T v)
""")
    text = text.replace("(mul_le_mul_right hnorm).mp hcancel",
                        "(mul_le_mul_right hnorm).1 hcancel")

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
