from __future__ import annotations

from pathlib import Path

import apply_one_hundred_twenty_fourth_pass_repairs as pass124
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
            """set_option maxHeartbeats 800000 in
theorem evidenceClass_exhaustive (r : AdvancedClaimsIIRequirement) :
    r.evidenceClass = .finiteExact /\\
        List.Mem r finiteExactRequirements \/
      r.evidenceClass = .analyticBoundary /\\
          List.Mem r analyticBoundaryRequirements \/
        r.evidenceClass = .diagnosticMetadata /\\
            List.Mem r diagnosticMetadataRequirements \/
          r.evidenceClass = .aggregate /\\
            List.Mem r aggregateRequirements := by
  cases r <;>
    simp_all [finiteExactRequirements, analyticBoundaryRequirements,
      diagnosticMetadataRequirements, aggregateRequirements, all, evidenceClass] <;>
    simp only [List.mem_cons, true_or, or_true]
""",
            """set_option maxHeartbeats 800000 in
theorem evidenceClass_exhaustive (r : AdvancedClaimsIIRequirement) :
    r.evidenceClass = .finiteExact /\\
        List.Mem r finiteExactRequirements \/
      r.evidenceClass = .analyticBoundary /\\
          List.Mem r analyticBoundaryRequirements \/
        r.evidenceClass = .diagnosticMetadata /\\
            List.Mem r diagnosticMetadataRequirements \/
          r.evidenceClass = .aggregate /\\
            List.Mem r aggregateRequirements := by
  have hr : List.Mem r all := mem_all r
  cases hclass : r.evidenceClass with
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
            1,
            "Mock1Advanced classify every requirement through the existing complete registry",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """  map_smul' c x := by
    change
      c * (inverseEvalLinear A q x.2.2) +
          c * (evalLinear A q x.2.1) =
        (inverseEvalLinear A q x.2.2) * c +
          (evalLinear A q x.2.1) * c
    ring
""",
            """  map_smul' c x := by
    change
      (inverseEvalLinear A q) (c • x.2.2) +
          (evalLinear A q) (c • x.2.1) =
        c • ((inverseEvalLinear A q) x.2.2 +
          (evalLinear A q) x.2.1)
    simp
""",
            1,
            "Mock2 expose product scalar multiplication before using linear-map homogeneity",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """theorem kernel_integrable (m i : ℕ) :
    Integrable (kernel m i) (Measure.dirac (0 : ℝ)) := by
  exact integrable_dirac continuous_const.aestronglyMeasurable
""",
            """theorem kernel_integrable (m i : ℕ) :
    Integrable (kernel m i) (Measure.dirac (0 : ℝ)) := by
  apply integrable_dirac
  simp [kernel]
""",
            1,
            "Mock2Advanced prove the finite Dirac value required by integrable_dirac",
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
deriving DecidableEq, Fintype
""",
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
            1,
            "FunctionalAnalysis separate finite existence from noncomputable enumeration",
        ),
        (
            """noncomputable def gammaTwoActualPolygonEdgeBoundaryParametrization
    (e : GammaTwoActualPolygonEdge) :
    GammaTwoBoundaryParametrization where
  kind := e.2.kind
  parameterSet := modularTileEdgeParameterSet e.2
  endpoints := modularTileEdgeEndpoints e.2
  point t := if ht : t ∈ modularTileEdgeParameterSet e.2 then
      gammaTwoActualPolygonEdgeParam e ⟨t, ht⟩
    else UpperHalfPlane.I
  target := gammaTwoActualPolygonEdgeSet e
  mapsTo := by
    intro t ht
    rw [dif_pos ht]
    exact gammaTwoActualPolygonEdgeParam_mem e ⟨t, ht⟩
""",
            """noncomputable def gammaTwoActualPolygonEdgeBoundaryParametrization
    (e : GammaTwoActualPolygonEdge) :
    GammaTwoBoundaryParametrization := by
  classical
  exact
    { kind := e.2.kind
      parameterSet := modularTileEdgeParameterSet e.2
      endpoints := modularTileEdgeEndpoints e.2
      point := fun t => if ht : t ∈ modularTileEdgeParameterSet e.2 then
          gammaTwoActualPolygonEdgeParam e ⟨t, ht⟩
        else UpperHalfPlane.I
      target := gammaTwoActualPolygonEdgeSet e
      mapsTo := by
        intro t ht
        simp only [dif_pos ht]
        exact gammaTwoActualPolygonEdgeParam_mem e ⟨t, ht⟩ }
""",
            1,
            "FunctionalAnalysis enable classical membership only inside the noncomputable edge package",
        ),
        (
            """  mapsTo := by
    intro t ht
    rw [dif_pos (ha.trans_le ht.1)]
    exact gammaTwoStandardEdgeParam_mem e ⟨t, ha.trans_le ht.1⟩
""",
            """  mapsTo := by
    intro t ht
    simpa only [dif_pos (ha.trans_le ht.1)] using
      gammaTwoStandardEdgeParam_mem e ⟨t, ha.trans_le ht.1⟩
""",
            1,
            "FunctionalAnalysis beta-reduce the dependent positive-parameter branch",
        ),
    ])


def main() -> int:
    pass124.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
