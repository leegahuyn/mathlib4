from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """/-- Global affine parametrization of the left vertical line. -/
def modularLeftVerticalCurve (t : ℝ) : ℂ :=
""",
        """section StandardComplexRealNormedSpace

local attribute [-instance] instInnerProductSpaceRealComplex
local attribute [instance 2000] NormedSpace.complexToReal

/-- Global affine parametrization of the left vertical line. -/
def modularLeftVerticalCurve (t : ℝ) : ℂ :=
""",
        "Mock2 Advanced use the standard real NormedSpace on complex boundary curves",
    )
    m2a = replace_exact(
        m2a,
        """end CorrectedLemmas.Gamma2SixCellPolygon

/-! ### Unconditional generation of `Gamma(2)`
""",
        """end StandardComplexRealNormedSpace

end CorrectedLemmas.Gamma2SixCellPolygon

/-! ### Unconditional generation of `Gamma(2)`
""",
        "Mock2 Advanced close the standard complex-real NormedSpace section",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
