from __future__ import annotations

from pathlib import Path

import apply_one_hundred_twenty_fifth_pass_repairs as pass125
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
            """  cases hclass : r.evidenceClass with
  | finiteExact =>
      exact Or.inl ⟨hclass, by
        simp [finiteExactRequirements, hr, hclass]⟩
  | analyticBoundary =>
      exact Or.inr (Or.inl ⟨hclass, by
        simp [analyticBoundaryRequirements, hr, hclass]⟩)
  | diagnosticMetadata =>
      exact Or.inr (Or.inr (Or.inl ⟨hclass, by
        simp [diagnosticMetadataRequirements, hr, hclass]⟩))
  | aggregate =>
      exact Or.inr (Or.inr (Or.inr ⟨hclass, by
        simp [aggregateRequirements, hr, hclass]⟩))
""",
            """  cases hclass : r.evidenceClass with
  | finiteExact =>
      exact Or.inl ⟨rfl, by
        apply List.mem_filter.mpr
        exact ⟨hr, by simp [hclass]⟩⟩
  | analyticBoundary =>
      exact Or.inr (Or.inl ⟨rfl, by
        apply List.mem_filter.mpr
        exact ⟨hr, by simp [hclass]⟩⟩)
  | diagnosticMetadata =>
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by
        apply List.mem_filter.mpr
        exact ⟨hr, by simp [hclass]⟩⟩))
  | aggregate =>
      exact Or.inr (Or.inr (Or.inr ⟨rfl, by
        apply List.mem_filter.mpr
        exact ⟨hr, by simp [hclass]⟩⟩))
""",
            1,
            "Mock1Advanced separate the substituted class equality from filter membership",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """    simp

/-- The complex module of convergent homogeneous variations.""",
            """    ring

/-- The complex module of convergent homogeneous variations.""",
            1,
            "Mock2 close homogeneous scalar compatibility by distributivity",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  apply integrable_dirac
  simp [kernel]
""",
            """  apply integrable_dirac
  positivity
""",
            1,
            "Mock2Advanced prove strict finiteness of the geometric Dirac value",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """inductive GammaTwoTruncationBoundaryPiece
  | circularArc (q : GammaTwoRightCoset)
  | leftVerticalSegment (q : GammaTwoRightCoset)
  | rightVerticalSegment (q : GammaTwoRightCoset)
  | horocycleSegment (q : GammaTwoRightCoset)
deriving Finite

noncomputable instance gammaTwoTruncationBoundaryPieceDecidableEq :
    DecidableEq GammaTwoTruncationBoundaryPiece :=
  Classical.decEq _

noncomputable instance gammaTwoTruncationBoundaryPieceFintype :
    Fintype GammaTwoTruncationBoundaryPiece :=
  Fintype.ofFinite _
""",
            """inductive GammaTwoTruncationBoundaryPiece
  | circularArc (q : GammaTwoRightCoset)
  | leftVerticalSegment (q : GammaTwoRightCoset)
  | rightVerticalSegment (q : GammaTwoRightCoset)
  | horocycleSegment (q : GammaTwoRightCoset)

noncomputable instance gammaTwoTruncationBoundaryPieceDecidableEq :
    DecidableEq GammaTwoTruncationBoundaryPiece :=
  Classical.decEq _

noncomputable instance gammaTwoTruncationBoundaryPieceFinite :
    Finite GammaTwoTruncationBoundaryPiece := by
  let encode : GammaTwoTruncationBoundaryPiece →
      Fin 4 × GammaTwoRightCoset
    | .circularArc q => (0, q)
    | .leftVerticalSegment q => (1, q)
    | .rightVerticalSegment q => (2, q)
    | .horocycleSegment q => (3, q)
  exact Finite.of_injective encode (by
    intro a b hab
    cases a <;> cases b <;> simp_all [encode])

noncomputable instance gammaTwoTruncationBoundaryPieceFintype :
    Fintype GammaTwoTruncationBoundaryPiece :=
  Fintype.ofFinite _
""",
            1,
            "FunctionalAnalysis build finiteness from an injective four-tag encoding",
        ),
    ])


def main() -> int:
    pass125.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
