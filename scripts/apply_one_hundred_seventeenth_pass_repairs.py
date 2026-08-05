from __future__ import annotations

from pathlib import Path

import apply_one_hundred_sixteenth_pass_repairs as pass116
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


def repair_mock1_advanced() -> None:
    apply_replacements(ROOT / "Mock1_Advanced.lean", [
        (
            """  classical
  cases r <;>
    simp [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass]
""",
            """  classical
  cases r <;>
    simp [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass] <;>
    decide
""",
            1,
            "Mock1Advanced close each computed requirement-membership branch by kernel reduction",
        ),
        (
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  intro h
  have hm : List.Mem objectClaimRegistry finiteExactRequirements := by
    simp [finiteExactRequirements, all, evidenceClass]
  simpa [h] using hm
""",
            """theorem finiteExactRequirements_nonempty :
    Not (finiteExactRequirements = []) := by
  decide
""",
            1,
            "Mock1Advanced compute finite-exact nonemptiness directly",
        ),
        (
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  intro h
  have hm : List.Mem principalPartRationalSolve analyticBoundaryRequirements := by
    simp [analyticBoundaryRequirements, all, evidenceClass]
  simpa [h] using hm
""",
            """theorem analyticBoundaryRequirements_nonempty :
    Not (analyticBoundaryRequirements = []) := by
  decide
""",
            1,
            "Mock1Advanced compute analytic-boundary nonemptiness directly",
        ),
        (
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  intro h
  have hm : List.Mem regressionCardySkeleton diagnosticMetadataRequirements := by
    simp [diagnosticMetadataRequirements, all, evidenceClass]
  simpa [h] using hm
""",
            """theorem diagnosticMetadataRequirements_nonempty :
    Not (diagnosticMetadataRequirements = []) := by
  decide
""",
            1,
            "Mock1Advanced compute diagnostic-metadata nonemptiness directly",
        ),
        (
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  intro h
  have hm : List.Mem namedConcretePaperInstance aggregateRequirements := by
    simp [aggregateRequirements, all, evidenceClass]
  simpa [h] using hm
""",
            """theorem aggregateRequirements_nonempty :
    Not (aggregateRequirements = []) := by
  decide
""",
            1,
            "Mock1Advanced compute aggregate nonemptiness directly",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """  res_id :
    ∀ (U : TopologicalSpace.Opens X) (s : obj U),
      res (le_refl U) s = s
  res_comp :
    ∀ {U V W : TopologicalSpace.Opens X}
      (hUV : U ≤ V) (hVW : V ≤ W) (s : obj W),
      res hUV (res hVW s) = res (le_trans hUV hVW) s
""",
            """  res_id :
    ∀ (U : TopologicalSpace.Opens X) (s : obj U),
      (@res U U (le_refl U)) s = s
  res_comp :
    ∀ {U V W : TopologicalSpace.Opens X}
      (hUV : U ≤ V) (hVW : V ≤ W) (s : obj W),
      (@res U V hUV) ((@res V W hVW) s) =
        (@res U W (le_trans hUV hVW)) s
""",
            1,
            "Mock2 make restriction-field open-set arguments explicit inside the structure",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """    (by simpa only [Pi.mul_apply] using
      (hbcomp.mul_right (f' := narrowSmoothTentFunction T hT)))
""",
            """    (by
      change HasCompactSupport
        (narrowSmoothTentFunction T hT * narrowSmoothTentFunction T hT)
      exact hbcomp.mul_right (f' := narrowSmoothTentFunction T hT))
""",
            1,
            "Mock2Advanced retain the pointwise product form for compact support",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """    subst x
    exact le_rfl
""",
            """    subst x
    change (0 : ℝ) ≤ 0
    exact le_rfl
""",
            2,
            "FunctionalAnalysis expose both vertical endpoint goals as real inequalities",
        ),
    ])


def main() -> int:
    pass116.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
