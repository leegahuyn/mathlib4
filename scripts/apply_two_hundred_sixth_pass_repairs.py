from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
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
    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem toSmoothCompactWeightCore_apply (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    (toSmoothCompactWeightCore n u).toSection z =
      (u : SmoothQuotientCompactFunction) z :=
  rfl
""",
        """theorem toSmoothCompactWeightCore_apply (n : ℤ)
    (u : InverseEtaFixedPhaseCore n) (z : ℍ) :
    SmoothCompactWeightCore.toSection
        (toSmoothCompactWeightCore n u) z =
      (u : SmoothQuotientCompactFunction) z :=
  rfl
""",
        "FunctionalAnalysis call the smooth compact core projection explicitly",
    )
    fa = replace_exact(
        fa,
        """  have h := congrArg
    (fun w : SmoothCompactWeightCore
        (inverseEtaPaperOrbitMultiplier
          GammaTwoQuotientGeometry.GammaTwo n) => w.toSection z) huv
""",
        """  have h := congrArg
    (fun w : SmoothCompactWeightCore
        (inverseEtaPaperOrbitMultiplier
          GammaTwoQuotientGeometry.GammaTwo n) =>
      SmoothCompactWeightCore.toSection w z) huv
""",
        "FunctionalAnalysis use the explicit projection in the injectivity proof",
    )
    fa = replace_exact(
        fa,
        "Submodule.codRestrict",
        "LinearMap.codRestrict",
        "FunctionalAnalysis update linear-map codomain restriction API",
        expected=4,
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
