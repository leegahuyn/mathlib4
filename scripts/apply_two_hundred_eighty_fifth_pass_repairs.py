from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    text = M2.read_text(encoding="utf-8")
    text = replace_exact(
        text,
        """    rw [OnePoint.smul_infty_eq_ite, if_neg hc]
    simpa only [OnePoint.some_eq_iff] using hdiv
""",
        """    rw [OnePoint.smul_infty_eq_ite, if_neg hc]
    intro h
    exact hdiv (OnePoint.coe_injective h)
""",
        "Mock2 use injectivity of the finite-point embedding",
    )
    text = replace_exact(
        text,
        """  change twoComponentAnalyticData.totalOperator u = 0
  apply WithLp.ofLp_injective 2
  simp [AnalyticData.totalOperator, twoComponentAnalyticData,
    firstCoordinateOperator, u]
""",
        """  change firstCoordinateOperator u + 0 = 0
  simp only [add_zero]
  apply WithLp.ofLp_injective 2
  ext <;> simp [firstCoordinateOperator, u]
""",
        "Mock2 evaluate the vertical kernel vector componentwise",
    )
    text = replace_exact(
        text,
        "abbrev ConcreteGaugeModel : ModelWithCorners ℂ ℂ ℂ := 𝓘(ℂ)",
        "noncomputable abbrev ConcreteGaugeModel : ModelWithCorners ℂ ℂ ℂ := 𝓘(ℂ)",
        "Mock2 mark the concrete gauge model noncomputable",
    )
    text = replace_exact(
        text,
        """structure ShEq (X : Type u) [TopologicalSpace X] where
  ambient : QGaugePresheaf (Opens X)
  boundary : QGaugePresheaf (Opens X)
""",
        """structure ShEq (X : Type u) [TopologicalSpace X] where
  ambient : QGaugePresheaf.{u, v} (Opens X)
  boundary : QGaugePresheaf.{u, v} (Opens X)
""",
        "Mock2 pin the equalizer-sheaf field universe",
    )
    M2.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
