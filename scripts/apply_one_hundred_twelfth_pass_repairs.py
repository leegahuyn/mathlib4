from __future__ import annotations

from pathlib import Path

import apply_one_hundred_eleventh_pass_repairs as pass111
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
            """  cases hblock with
  | head => simp [referenceMock1MList, referenceMock1RPhases,
      List.mem_cons, List.mem_singleton]
  | tail _ hblock =>
      cases hblock with
      | head => simp [referenceMock1MList, referenceMock1RPhases,
          List.mem_cons, List.mem_singleton]
      | tail _ hblock =>
          cases hblock with
          | head => simp [referenceMock1MList, referenceMock1RPhases,
              List.mem_cons, List.mem_singleton]
          | tail _ hnil => cases hnil
""",
            """  cases hblock with
  | head =>
      exact And.intro
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.head _)))))))
        (List.Mem.head _)
  | tail _ hblock =>
      cases hblock with
      | head =>
          exact And.intro
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
                (List.Mem.tail _ (List.Mem.tail _
                  (List.Mem.head _)))))))))
            (List.Mem.head _)
      | tail _ hblock =>
          cases hblock with
          | head =>
              exact And.intro
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
                  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
                    (List.Mem.head _)))))))
                (List.Mem.tail _ (List.Mem.head _))
          | tail _ hnil => cases hnil
""",
            1,
            "Mock1Advanced construct all weighted-block memberships explicitly",
        ),
        (
            """  cases r <;>
    simp [evidenceClass, finiteExactRequirements,
      analyticBoundaryRequirements, diagnosticMetadataRequirements,
      aggregateRequirements, all, List.mem_cons, List.mem_singleton]
""",
            """  cases r <;> decide
""",
            1,
            "Mock1Advanced decide the finite exhaustive requirement classification",
        ),
        (
            """structure AdvancedClaimsIIRamanujanFActualCertificateConstructorBoundary : Prop where
""",
            """structure AdvancedClaimsIIRamanujanFActualCertificateConstructorBoundary where
""",
            1,
            "Mock1Advanced place the constructor boundary in Type because it stores data",
        ),
        (
            """theorem concrete_at
    (C : AdvancedClaimsIIRamanujanFActualCertificateConstructorBoundary)
""",
            """def concrete_at
    (C : AdvancedClaimsIIRamanujanFActualCertificateConstructorBoundary)
""",
            1,
            "Mock1Advanced expose the stored concrete certificate as a definition",
        ),
        (
            """theorem reference_advanced_claims_ii_ramanujan_f_actual_constructor_boundary :
    AdvancedClaimsIIRamanujanFActualCertificateConstructorBoundary where
""",
            """noncomputable def reference_advanced_claims_ii_ramanujan_f_actual_constructor_boundary :
    AdvancedClaimsIIRamanujanFActualCertificateConstructorBoundary where
""",
            1,
            "Mock1Advanced define the concrete constructor boundary as data",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """theorem add_convergesAt {a b : QSeries} {q : ℂ}
    (ha : a.ConvergesAt q) (hb : b.ConvergesAt q) :
    (a + b).ConvergesAt q := by
  simpa [ConvergesAt, term, add_mul] using ha.add hb
""",
            """theorem add_convergesAt {a b : QSeries} {q : ℂ}
    (ha : a.ConvergesAt q) (hb : b.ConvergesAt q) :
    (a + b).ConvergesAt q := by
  change Summable (fun n : ℕ => (a n + b n) * q ^ n)
  change Summable (fun n : ℕ => a n * q ^ n) at ha
  change Summable (fun n : ℕ => b n * q ^ n) at hb
  simpa only [add_mul] using ha.add hb
""",
            1,
            "Mock2 expose pointwise q-series addition before summability",
        ),
        (
            """theorem smul_convergesAt (c : ℂ) {a : QSeries} {q : ℂ}
    (ha : a.ConvergesAt q) :
    (c • a).ConvergesAt q := by
  simpa [ConvergesAt, term, smul_eq_mul, mul_assoc] using
    (Summable.const_smul c ha)
""",
            """theorem smul_convergesAt (c : ℂ) {a : QSeries} {q : ℂ}
    (ha : a.ConvergesAt q) :
    (c • a).ConvergesAt q := by
  change Summable (fun n : ℕ => (c * a n) * q ^ n)
  change Summable (fun n : ℕ => a n * q ^ n) at ha
  simpa only [mul_assoc] using (Summable.const_smul c ha)
""",
            1,
            "Mock2 expose pointwise scalar multiplication before summability",
        ),
        (
            """  res_id :
    ∀ U : TopologicalSpace.Opens X,
      res (le_refl U) = 𝟙 (obj U)
  res_comp :
    ∀ {U V W : TopologicalSpace.Opens X}
      (hUV : U ≤ V) (hVW : V ≤ W),
      res hVW ≫ res hUV = res (le_trans hUV hVW)
""",
            """  res_id :
    ∀ U : TopologicalSpace.Opens X,
      res (U := U) (V := U) (le_refl U) = 𝟙 (obj U)
  res_comp :
    ∀ {U V W : TopologicalSpace.Opens X}
      (hUV : U ≤ V) (hVW : V ≤ W),
      res (U := V) (V := W) hVW ≫
          res (U := U) (V := V) hUV =
        res (U := U) (V := W) (le_trans hUV hVW)
""",
            1,
            "Mock2 make all restriction-domain arguments explicit in LinearPresheaf",
        ),
    ])


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  rw [hzero]
  change ∀ᶠ t : ℝ in (⊥ : Filter ℝ),
    K.normalization t * K.kernel t x = (0 : ℂ)
  exact Filter.eventually_bot
""",
            """  rw [hzero, MeasureTheory.aeEq_iff]
  simp
""",
            1,
            "Mock2Advanced reduce zero-measure a.e. equality to a zero measure set",
        ),
        (
            """  exact contDiff_const.mul (smoothTentBump T hT).contDiff
""",
            """  exact contDiff_const.mul
    ((smoothTentBump T hT).contDiff (n := (⊤ : ℕ∞)))
""",
            1,
            "Mock2Advanced instantiate bump smoothness at infinite finite order",
        ),
        (
            """  simpa only [smoothTentBumpFunction, Pi.mul_apply] using
    (HasCompactSupport.mul_left
      (f := fun _ : ℝ => T / 2)
      (smoothTentBump T hT).hasCompactSupport)
""",
            """  change HasCompactSupport
    ((T / 2 : ℝ) • (fun t : ℝ => smoothTentBump T hT t))
  exact (smoothTentBump T hT).hasCompactSupport.smul_left
""",
            1,
            "Mock2Advanced express the constant multiple through scalar action",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    wrong_count = text.count("ContDiff ℝ ⊤")
    right_count = text.count("ContDiff ℝ (↑(⊤ : ℕ∞))")
    if wrong_count == 16:
        text = text.replace("ContDiff ℝ ⊤", "ContDiff ℝ (↑(⊤ : ℕ∞))")
        changed = True
        print("Mock2Advanced restore sixteen C-infinity orders: applied 16")
    elif right_count >= 16:
        print("Mock2Advanced restore sixteen C-infinity orders: already applied")
    else:
        raise RuntimeError(
            f"Mock2Advanced C-infinity order count unexpected: wrong={wrong_count}, right={right_count}"
        )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """            apply iUnion_congr
            intro q
""",
            """            apply Set.iUnion_congr
            intro q
""",
            1,
            "FunctionalAnalysis use the namespaced indexed-union congruence theorem",
        ),
        (
            """inductive GammaTwoBoundaryPieceKind
  | circularArc
  | verticalSegment
  | horocycleSegment
deriving DecidableEq, Fintype
""",
            """inductive GammaTwoBoundaryPieceKind
  | circularArc
  | verticalSegment
  | horocycleSegment
deriving DecidableEq

instance gammaTwoBoundaryPieceKindFintype :
    Fintype GammaTwoBoundaryPieceKind where
  elems := {.circularArc, .verticalSegment, .horocycleSegment}
  complete x := by cases x <;> simp
""",
            1,
            "FunctionalAnalysis define the boundary-piece Fintype explicitly",
        ),
        (
            """inductive GammaTwoModularTileEdge
  | circularArc
  | leftVerticalSegment
  | rightVerticalSegment
deriving DecidableEq, Fintype
""",
            """inductive GammaTwoModularTileEdge
  | circularArc
  | leftVerticalSegment
  | rightVerticalSegment
deriving DecidableEq

instance gammaTwoModularTileEdgeFintype :
    Fintype GammaTwoModularTileEdge where
  elems := {.circularArc, .leftVerticalSegment, .rightVerticalSegment}
  complete x := by cases x <;> simp
""",
            1,
            "FunctionalAnalysis define the modular-edge Fintype explicitly",
        ),
    ])


def main() -> int:
    pass111.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
