from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirtieth_pass_repairs as pass130
import apply_one_hundred_thirty_first_pass_repairs as pass131
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
            """def gammaTwoVerticalIncidencePolynomial
""",
            """noncomputable def gammaTwoVerticalIncidencePolynomial
""",
            1,
            "FunctionalAnalysis mark the vertical polynomial definition noncomputable",
        ),
        (
            """def gammaTwoCircularIncidencePolynomial
""",
            """noncomputable def gammaTwoCircularIncidencePolynomial
""",
            1,
            "FunctionalAnalysis mark the circular polynomial definition noncomputable",
        ),
        (
            """    simpa [gammaTwoVerticalIncidencePolynomial, hc] using hcoeff
""",
            """    norm_num [gammaTwoVerticalIncidencePolynomial, hc] at hcoeff
""",
            1,
            "FunctionalAnalysis compute the vertical linear coefficient in the zero-c case",
        ),
        (
            """    exact hlead (by
      simpa [gammaTwoVerticalIncidencePolynomial] using hcoeff)
""",
            """    apply hlead
    norm_num [gammaTwoVerticalIncidencePolynomial] at hcoeff ⊢
    exact hcoeff
""",
            1,
            "FunctionalAnalysis compute the vertical quadratic coefficient explicitly",
        ),
        (
            """  exact hlead (by
    simpa [gammaTwoCircularIncidencePolynomial] using hcoeff)
""",
            """  apply hlead
  norm_num [gammaTwoCircularIncidencePolynomial] at hcoeff ⊢
  exact hcoeff
""",
            1,
            "FunctionalAnalysis compute the circular quadratic coefficient explicitly",
        ),
        (
            """  rw [Polynomial.IsRoot.def,
    gammaTwoCircularIncidencePolynomial_eval]
""",
            """  change Polynomial.eval (t : ℝ)
      (gammaTwoCircularIncidencePolynomial
        (gammaTwoCuspLevel Y)
        (gammaTwoCornerLowerLeft (e, .circularArc) q ^ 2 +
          gammaTwoCornerLowerRight (e, .circularArc) q ^ 2)
        (gammaTwoCornerLowerLeft (e, .circularArc) q *
          gammaTwoCornerLowerRight (e, .circularArc) q)) = 0
  rw [gammaTwoCircularIncidencePolynomial_eval]
""",
            1,
            "FunctionalAnalysis expose the circular root goal as polynomial evaluation",
        ),
        (
            """theorem gammaTwoLeftVerticalSelectedCurveParameters_subset_isRoot
    (Y : ℝ) (e : GammaTwoRightCoset)
    (q : GammaTwoRightCoset) :
    gammaTwoActualEdgeSelectedCurveParameters Y
        (e, .leftVerticalSegment) q ⊆
      {t : Set.Ici (0 : ℝ) |
        Polynomial.IsRoot
          (gammaTwoVerticalIncidencePolynomial
            (gammaTwoCuspLevel Y)
            (gammaTwoCornerLowerLeft (e, .leftVerticalSegment) q)
            (gammaTwoCornerLowerRight (e, .leftVerticalSegment) q)
            (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2))
          (t : ℝ)} := by
  intro t ht
  rw [Polynomial.IsRoot.def,
    gammaTwoVerticalIncidencePolynomial_eval]
""",
            """theorem gammaTwoLeftVerticalSelectedCurveParameters_subset_isRoot
    (Y : ℝ) (e : GammaTwoRightCoset)
    (q : GammaTwoRightCoset) :
    gammaTwoActualEdgeSelectedCurveParameters Y
        (e, .leftVerticalSegment) q ⊆
      {t : Set.Ici (0 : ℝ) |
        Polynomial.IsRoot
          (gammaTwoVerticalIncidencePolynomial
            (gammaTwoCuspLevel Y)
            (gammaTwoCornerLowerLeft (e, .leftVerticalSegment) q)
            (gammaTwoCornerLowerRight (e, .leftVerticalSegment) q)
            (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2))
          (t : ℝ)} := by
  intro t ht
  change Polynomial.eval (t : ℝ)
      (gammaTwoVerticalIncidencePolynomial
        (gammaTwoCuspLevel Y)
        (gammaTwoCornerLowerLeft (e, .leftVerticalSegment) q)
        (gammaTwoCornerLowerRight (e, .leftVerticalSegment) q)
        (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2)) = 0
  rw [gammaTwoVerticalIncidencePolynomial_eval]
""",
            1,
            "FunctionalAnalysis expose the left vertical root goal as polynomial evaluation",
        ),
        (
            """theorem gammaTwoRightVerticalSelectedCurveParameters_subset_isRoot
    (Y : ℝ) (e : GammaTwoRightCoset)
    (q : GammaTwoRightCoset) :
    gammaTwoActualEdgeSelectedCurveParameters Y
        (e, .rightVerticalSegment) q ⊆
      {t : Set.Ici (0 : ℝ) |
        Polynomial.IsRoot
          (gammaTwoVerticalIncidencePolynomial
            (gammaTwoCuspLevel Y)
            (gammaTwoCornerLowerLeft (e, .rightVerticalSegment) q)
            (gammaTwoCornerLowerRight (e, .rightVerticalSegment) q)
            ((1 : ℝ) / 2) (Real.sqrt 3 / 2))
          (t : ℝ)} := by
  intro t ht
  rw [Polynomial.IsRoot.def,
    gammaTwoVerticalIncidencePolynomial_eval]
""",
            """theorem gammaTwoRightVerticalSelectedCurveParameters_subset_isRoot
    (Y : ℝ) (e : GammaTwoRightCoset)
    (q : GammaTwoRightCoset) :
    gammaTwoActualEdgeSelectedCurveParameters Y
        (e, .rightVerticalSegment) q ⊆
      {t : Set.Ici (0 : ℝ) |
        Polynomial.IsRoot
          (gammaTwoVerticalIncidencePolynomial
            (gammaTwoCuspLevel Y)
            (gammaTwoCornerLowerLeft (e, .rightVerticalSegment) q)
            (gammaTwoCornerLowerRight (e, .rightVerticalSegment) q)
            ((1 : ℝ) / 2) (Real.sqrt 3 / 2))
          (t : ℝ)} := by
  intro t ht
  change Polynomial.eval (t : ℝ)
      (gammaTwoVerticalIncidencePolynomial
        (gammaTwoCuspLevel Y)
        (gammaTwoCornerLowerLeft (e, .rightVerticalSegment) q)
        (gammaTwoCornerLowerRight (e, .rightVerticalSegment) q)
        ((1 : ℝ) / 2) (Real.sqrt 3 / 2)) = 0
  rw [gammaTwoVerticalIncidencePolynomial_eval]
""",
            1,
            "FunctionalAnalysis expose the right vertical root goal as polynomial evaluation",
        ),
    ])


def main() -> int:
    pass130.main()
    pass131.repair_mock1_advanced()
    pass131.repair_mock2()
    pass131.repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
