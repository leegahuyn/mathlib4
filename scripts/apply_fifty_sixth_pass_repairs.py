from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(text: str, old: str, new: str, expected: int, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == expected:
        print(f"{label}: applied {count}")
        return text.replace(old, new), True
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count == 0:
        print(f"{label}: source changed; skipped")
        return text, False
    raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")


def replace_region(
    text: str, start: str, end: str, replacement: str, label: str
) -> tuple[str, bool]:
    i = text.find(start)
    if i < 0:
        if replacement in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: start marker absent; skipped")
        return text, False
    j = text.find(end, i)
    if j < 0:
        raise RuntimeError(f"{label}: end marker absent")
    old = text[i:j]
    if old == replacement:
        print(f"{label}: already applied")
        return text, False
    print(f"{label}: applied")
    return text[:i] + replacement + text[j:], True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacement = r'''theorem padic_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    (Not (referenceT1DenominatorNonzero.denominator = 0) /\
      Not (referenceT2LeadingDenominatorNonzero.denominator = 0) /\
        Not (referenceT2SimpleDenominatorNonzero.denominator = 0)) /\
      (forall n, FiniteCongruenceMod C.padicChart.p C.padicChart.k
        (C.padicChart.chartLeft n) (C.padicChart.chartRight n)) /\
      (forall n,
        FiniteCongruenceMod
            C.paperInstance.extraction.concrete.mahlerBinomial.p
            C.paperInstance.extraction.concrete.mahlerBinomial.k
            (C.paperInstance.extraction.concrete.mahlerBinomial.eval n)
            (C.paperInstance.extraction.concrete.mahlerBinomial.target n) /\
          C.paperInstance.extraction.concrete.mahlerBinomial.eval n =
            Finset.sum Finset.univ
              (fun j : Fin C.paperInstance.extraction.concrete.mahlerBinomial.length =>
                C.paperInstance.extraction.concrete.mahlerBinomial.coeff j *
                  mahlerBinomialBasis (j : Nat) n)) /\
      (forall n, C.padicAnalyticRange.cutoff <= n ->
        C.padicAnalyticRange.predicate n) /\
      (C.sptKernel.sptFree.spt.obstruction.order = 1 /\
        Not (C.sptKernel.sptFailure.spt.obstruction.order = 1)) :=
'''
    text, did = replace_region(
        text,
        "theorem padic_actual_inputs_at\n",
        "  And.intro A.denominator_clearing_data\n",
        replacement,
        "Mock1Advanced state p-adic audit with proposition types",
    )
    changed |= did

    replacement = r'''theorem entropy_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    C.entropy.symbolic.alphaInterval.Contains C.entropy.symbolic.alphaHat /\
      (forall n, C.entropy.entropy.degeneracy.degeneracy n =
        C.entropy.entropy.degeneracy.coefficient n) /\
      (C.entropy.entropy.olsTable.rows.length = 5 /\
        C.entropy.entropy.olsTable.alphaRow.interval.Contains
          C.entropy.entropy.olsTable.alphaRow.estimate /\
        C.entropy.entropy.olsTable.ceffRow.interval.Contains
          C.entropy.entropy.olsTable.ceffRow.estimate) /\
      C.tables.paperTables.externalScript.rows.length = 16 :=
'''
    text, did = replace_region(
        text,
        "theorem entropy_actual_inputs_at\n",
        "  And.intro A.actual_entropy_alpha_extraction\n",
        replacement,
        "Mock1Advanced state entropy audit with proposition types",
    )
    changed |= did

    old = """theorem mem_all (s : AdvancedClaimsIIObjectiveSection) :
    List.Mem s all := by
  cases s <;> simp [all]
"""
    new = """theorem mem_all (s : AdvancedClaimsIIObjectiveSection) :
    List.Mem s all := by
  cases s with
  | objectSchema => exact List.Mem.head _
  | t1t5Core => exact List.Mem.tail _ (List.Mem.head _)
  | sptEqualizerTorCrt => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | kernelCuspMultiplier =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | exactCoefficientFormula =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
  | pAdicSection =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  | entropyCardyReproducibility =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | paperDataInstance =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))
  | finalAggregation =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock1Advanced prove objective membership structurally",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """theorem paper_data_requirement_mem :
    List.Mem AdvancedClaimsIIRequirement.paperObjectDataInstance
      (requirements paperDataInstance) := by
  decide
""",
        """theorem paper_data_requirement_mem :
    List.Mem AdvancedClaimsIIRequirement.paperObjectDataInstance
      (requirements paperDataInstance) := by
  exact List.Mem.head _
""",
        1,
        "Mock1Advanced prove singleton paper-data requirement membership",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """        have hsrc :
            (p ^ shiftExponent M p k : ZMod (Pk p k)) *
                (z : ZMod (Pk p k)) =
              (((((p ^ shiftExponent M p k : ℕ) : ℤ) * z : ℤ)) :
                ZMod (Pk p k)) := by
          change
            (p : ZMod (Pk p k)) ^ shiftExponent M p k *
                (z : ZMod (Pk p k)) =
              (p : ZMod (Pk p k)) ^ shiftExponent M p k *
                (z : ZMod (Pk p k))
          rfl
"""
    new = """        have hsrc :
            (p ^ shiftExponent M p k : ZMod (Pk p k)) *
                (z : ZMod (Pk p k)) =
              (((((p ^ shiftExponent M p k : ℕ) : ℤ) * z : ℤ)) :
                ZMod (Pk p k)) := by
          simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2 normalize the source power cast by cast lemmas",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ac_rfl
""",
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring
""",
        1,
        "Mock2 close the commuting power-factor identity",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """abbrev integerModule : ModuleCat ℤ := 𝟙_ (ModuleCat ℤ)

/-- `ZMod n` regarded as a module over `ℤ`. -/
""",
        """abbrev integerModule : ModuleCat ℤ := 𝟙_ (ModuleCat ℤ)

/-- An explicit zero integer module used in categorical object positions. -/
abbrev zeroIntegerModule : ModuleCat ℤ :=
  ModuleCat.of ℤ (Fin 0 → ℤ)

/-- `ZMod n` regarded as a module over `ℤ`. -/
""",
        1,
        "Mock2 define the explicit zero integer module",
    )
    changed |= did

    normalized = text.rstrip() + "\n"
    if normalized != text:
        text = normalized
        changed = True
        print("Mock2 normalize final newline")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  rw [denseRange_inclusion_iff]
  intro x hx
  exact subset_closure hx
""",
        """  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  rw [denseRange_inclusion_iff]
  intro x hx
  exact hx
""",
        2,
        "Mock2Advanced identify topological-closure membership definitionally",
    )
    changed |= did

    old = """    change
      (Lp.compMeasurePreserving (⇑chart.coord.symm) hsymm)
          ((Lp.compMeasurePreserving (⇑chart.coord) hcoord) F) = F
    exact hcomp.symm.trans (Lp.compMeasurePreserving_id_apply F)
"""
    new = """    change
      (Lp.compMeasurePreserving (⇑chart.coord.symm) hsymm)
          ((Lp.compMeasurePreserving (⇑chart.coord) hcoord) F) = F
    rw [← Lp.compMeasurePreserving_id_apply F]
    simpa only [Function.comp_def, chart.coord.apply_symm_apply] using hcomp.symm
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2Advanced factor the forward-backward Lp identity",
    )
    changed |= did

    old = """    change
      (Lp.compMeasurePreserving (⇑chart.coord) hcoord)
          ((Lp.compMeasurePreserving (⇑chart.coord.symm) hsymm) u) = u
    exact hcomp.symm.trans (Lp.compMeasurePreserving_id_apply u)
"""
    new = """    change
      (Lp.compMeasurePreserving (⇑chart.coord) hcoord)
          ((Lp.compMeasurePreserving (⇑chart.coord.symm) hsymm) u) = u
    rw [← Lp.compMeasurePreserving_id_apply u]
    simpa only [Function.comp_def, chart.coord.symm_apply_apply] using hcomp.symm
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2Advanced factor the backward-forward Lp identity",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  norm_num [gammaTwoHyperbolic, UpperHalfPlane.I, UpperHalfPlane.denom,
    Matrix.SpecialLinearGroup.map, Matrix.SpecialLinearGroup.toGL,
    Complex.normSq]
""",
        """  norm_num [gammaTwoHyperbolic, UpperHalfPlane.I, UpperHalfPlane.denom,
    Matrix.SpecialLinearGroup.map, Matrix.SpecialLinearGroup.mapGL,
    Matrix.SpecialLinearGroup.toGL, Complex.normSq]
""",
        1,
        "FunctionalAnalysis unfold mapGL in the concrete Gamma(2) calculation",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
