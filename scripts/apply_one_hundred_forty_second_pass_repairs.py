from __future__ import annotations

from pathlib import Path

import apply_one_hundred_fortieth_pass_repairs as pass140
import apply_one_hundred_forty_first_pass_repairs as pass141
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """theorem inverseEtaRatio_continuous
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Continuous (inverseEtaRatio u) := by
  unfold inverseEtaRatio
  exact u.continuous.div continuous_inverseEtaSection
    inverseEtaSection_apply_ne_zero
""",
            """theorem inverseEtaRatio_continuous
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Continuous (inverseEtaRatio u) := by
  unfold inverseEtaRatio
  exact (SmoothCompactCore.continuous u).div continuous_inverseEtaSection
    inverseEtaSection_apply_ne_zero
""",
            1,
            "FunctionalAnalysis use the explicit core continuity theorem",
        ),
        (
            """theorem inverseEtaRatio_support
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Function.support (inverseEtaRatio u) =
      Function.support (u.toSection : ℍ → ℂ) := by
""",
            """theorem inverseEtaRatio_support
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Function.support (inverseEtaRatio u) =
      Function.support (SmoothCompactCore.toSection u : ℍ → ℂ) := by
""",
            1,
            "FunctionalAnalysis state inverse-eta support via the explicit projection",
        ),
        (
            """  rw [hγ z, WeightSection.covariance u γ z,
    WeightSection.covariance inverseEtaSection γ z]
""",
            """  rw [hγ z, SmoothCompactCore.covariance u γ z,
    WeightSection.covariance inverseEtaSection γ z]
""",
            1,
            "FunctionalAnalysis rewrite core covariance through its namespace theorem",
        ),
        (
            """theorem inverseEtaRatioQuotient_support
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Function.support (inverseEtaRatioQuotient u) =
      gammaTwoQuotientMk ''
        Function.support (u.toSection : ℍ → ℂ) := by
""",
            """theorem inverseEtaRatioQuotient_support
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    Function.support (inverseEtaRatioQuotient u) =
      gammaTwoQuotientMk ''
        Function.support (SmoothCompactCore.toSection u : ℍ → ℂ) := by
""",
            1,
            "FunctionalAnalysis state inverse-eta quotient support with explicit projection",
        ),
        (
            """    tsupport (inverseEtaRatioQuotient u) =
      quotientTSupport (u.toSection : ℍ → ℂ) := by
""",
            """    tsupport (inverseEtaRatioQuotient u) =
      quotientTSupport (SmoothCompactCore.toSection u : ℍ → ℂ) := by
""",
            1,
            "FunctionalAnalysis state quotient topological support explicitly",
        ),
        (
            """theorem inverseEtaRatioQuotient_hasCompactSupport
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    HasCompactSupport (inverseEtaRatioQuotient u) := by
  change IsCompact (tsupport (inverseEtaRatioQuotient u))
  rw [inverseEtaRatioQuotient_tsupport]
  exact u.quotientCompact
""",
            """theorem inverseEtaRatioQuotient_hasCompactSupport
    (u : SmoothCompactCore inverseEtaPaperCertificate) :
    HasCompactSupport (inverseEtaRatioQuotient u) := by
  change IsCompact (tsupport (inverseEtaRatioQuotient u))
  rw [inverseEtaRatioQuotient_tsupport]
  exact SmoothCompactCore.quotientCompact u
""",
            1,
            "FunctionalAnalysis use the explicit quotient compactness theorem",
        ),
        (
            """    inverseEtaQuotientScalar u (gammaTwoQuotientMk z) =
      u.toSection z / inverseEtaSection z :=
""",
            """    inverseEtaQuotientScalar u (gammaTwoQuotientMk z) =
      SmoothCompactCore.toSection u z / inverseEtaSection z :=
""",
            1,
            "FunctionalAnalysis expose the projected section in scalar evaluation",
        ),
        (
            """    inverseEtaQuotientLinear u (gammaTwoQuotientMk z) =
      u.toSection z / inverseEtaSection z :=
""",
            """    inverseEtaQuotientLinear u (gammaTwoQuotientMk z) =
      SmoothCompactCore.toSection u z / inverseEtaSection z :=
""",
            1,
            "FunctionalAnalysis expose the projected section in linear evaluation",
        ),
        (
            """  have hz :
      u.toSection z / inverseEtaSection z =
        v.toSection z / inverseEtaSection z := by
""",
            """  have hz :
      SmoothCompactCore.toSection u z / inverseEtaSection z =
        SmoothCompactCore.toSection v z / inverseEtaSection z := by
""",
            1,
            "FunctionalAnalysis formulate injectivity with explicit projected sections",
        ),
    ])


def main() -> int:
    pass140.main()
    pass141.repair_mock2()
    pass141.repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
