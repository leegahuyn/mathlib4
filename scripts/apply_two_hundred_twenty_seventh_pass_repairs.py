from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """    (by simpa only [one_mul, directionalDerivative_apply] using
      core_integrable (directionalDerivative ξ u))
""",
        """    (by
      exact (core_integrable (directionalDerivative ξ u)).congr
        (Filter.Eventually.of_forall fun x =>
          directionalDerivative_apply ξ u x))
""",
        "FunctionalAnalysis transport derivative integrability pointwise",
    )
    fa = replace_exact(
        fa,
        """  simpa only [one_mul, zero_mul, integral_zero, neg_zero,
    directionalDerivative_apply] using h
""",
        """  simpa only [one_mul, fderiv_const, zero_apply, zero_mul,
    integral_zero, neg_zero, directionalDerivative_apply] using h
""",
        "FunctionalAnalysis reduce the derivative of the constant test function",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
