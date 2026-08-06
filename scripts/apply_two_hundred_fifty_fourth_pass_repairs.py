from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


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
        """abbrev GaugeModel : ModelWithCorners ℂ ModelSpace ModelSpace := 𝓘(ℂ, ModelSpace)

instance gaugeGroupLieGroup : LieGroup GaugeModel ∞ GaugeGroup where
""",
        """abbrev GaugeModel : ModelWithCorners ℂ ModelSpace ModelSpace := 𝓘(ℂ, ModelSpace)

noncomputable local instance gaugeGroupChartedSpace :
    ChartedSpace ModelSpace GaugeGroup := by
  change ChartedSpace ModelSpace ModelSpace
  infer_instance

instance gaugeGroupLieGroup : LieGroup GaugeModel ∞ GaugeGroup where
""",
        "Mock2 transfer the self chart across the multiplicative type synonym",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """(ModularGroup.T ^ (2 : ℤ) : IntegralSpecialLinear)""",
        """(ModularGroup.T ^ (2 : ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ)""",
        "Mock2 Advanced type the T-squared action by the actual SL2 type",
    )
    m2a = replace_exact(
        m2a,
        """(ModularGroup.S⁻¹ : IntegralSpecialLinear)""",
        """(ModularGroup.S⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)""",
        "Mock2 Advanced type the inverse-S action by the actual SL2 type",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
