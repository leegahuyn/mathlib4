from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(
    text: str, old: str, new: str, expected: int, label: str
) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        "  rcases h with rfl | h\n",
        "  rcases List.mem_cons.mp h with rfl | h\n",
        108,
        "Mock1Advanced eliminate one constructor from each explicit membership proof",
    )
    changed |= did

    old = """theorem padic_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    PAdicRequirementPayloadCertificate.denominator_data_at
        C.pAdicRequirementPayload /\
      (forall n, PAdicRequirementPayloadCertificate.chart_vectors_at
          C.pAdicRequirementPayload n) /\
        (forall n, PAdicRequirementPayloadCertificate.mahler_table_at
            C.pAdicRequirementPayload n) /\
          (forall n, (hn : C.padicAnalyticRange.cutoff <= n) ->
            PAdicRequirementPayloadCertificate.predicate_at
              C.pAdicRequirementPayload n hn) /\
            PAdicRequirementPayloadCertificate.obstruction_failure_at
              C.pAdicRequirementPayload :=
"""
    new = """theorem padic_actual_inputs_at
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
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock1Advanced state the p-adic audit as propositions rather than proof terms",
    )
    changed |= did

    old = """theorem entropy_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    EntropyReproRequirementPayloadCertificate.alpha_extraction_at
        C.entropyReproRequirementPayload /\
      (forall n, EntropyReproRequirementPayloadCertificate.degeneracy_at
          C.entropyReproRequirementPayload n) /\
        EntropyReproRequirementPayloadCertificate.ols_interval_at
            C.entropyReproRequirementPayload /\
          EntropyReproRequirementPayloadCertificate.external_rows_at
            C.entropyReproRequirementPayload :=
"""
    new = """theorem entropy_actual_inputs_at
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
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock1Advanced state the entropy audit as propositions rather than proof terms",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """theorem mem_all (s : AdvancedClaimsIIObjectiveSection) :
    List.Mem s all := by
  cases s <;> decide
""",
        """theorem mem_all (s : AdvancedClaimsIIObjectiveSection) :
    List.Mem s all := by
  cases s <;> simp [all]
""",
        1,
        "Mock1Advanced prove objective membership by simplifying the closed list",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """          ring_nf
        have hexp :
""",
        """          change
            (p : ZMod (Pk p k)) ^ shiftExponent M p k *
                (z : ZMod (Pk p k)) =
              (p : ZMod (Pk p k)) ^ shiftExponent M p k *
                (z : ZMod (Pk p k))
          rfl
        have hexp :
""",
        1,
        "Mock2 normalize the source power cast definitionally",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring_nf
""",
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ac_rfl
""",
        1,
        "Mock2 reorder the two commuting power factors",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """abbrev integerModule : ModuleCat ℤ := 𝟙_ (ModuleCat ℤ)

/-- The residue module `ℤ/Mℤ`. -/
""",
        """abbrev integerModule : ModuleCat ℤ := 𝟙_ (ModuleCat ℤ)

/-- An explicit zero free integer module used in object positions. -/
abbrev zeroIntegerModule : ModuleCat ℤ :=
  ModuleCat.of ℤ (Fin 0 → ℤ)

/-- The residue module `ℤ/Mℤ`. -/
""",
        1,
        "Mock2 define an explicit zero module object",
    )
    changed |= did

    text, did = replace_exact(
        text,
        "(0 : ModuleCat ℤ)",
        "zeroIntegerModule",
        7,
        "Mock2 replace unsupported numeric zero objects",
    )
    changed |= did

    text, did = replace_exact(
        text,
        "  | _ + 2 => 0\n",
        "  | _ + 2 => zeroIntegerModule\n",
        1,
        "Mock2 use the explicit zero object in higher resolution degrees",
    )
    changed |= did

    old = """  intro x y hxy
  have hMZ : (M : ℤ) ≠ 0 := by exact_mod_cast hM
  change (M : ℤ) * x = (M : ℤ) * y at hxy
  exact mul_left_cancel₀ hMZ hxy
"""
    new = """  intro x y hxy
  have hMZ : (M : ℤ) ≠ 0 := by exact_mod_cast hM
  let x' : ℤ := x
  let y' : ℤ := y
  change (M : ℤ) * x' = (M : ℤ) * y' at hxy
  have hxy' : x' = y' := mul_left_cancel₀ hMZ hxy
  simpa [x', y'] using hxy'
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2 perform multiplication cancellation in the explicit integer type",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """  intro x hx
  exact M.core.le_topologicalClosure hx
""",
        """  intro x hx
  exact subset_closure hx
""",
        2,
        "Mock2Advanced use the ambient subset-closure theorem",
    )
    changed |= did

    old = """  have hstarInv := congrArg Inv.inv hstar
  rw [hstarInv]
"""
    new = """  rw [map_inv₀, hstar]
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2Advanced move the outer star through the inverse",
    )
    changed |= did

    old = """    simpa only [Function.comp_def, chart.coord.apply_symm_apply,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
"""
    new = """    exact hcomp.symm.trans (Lp.compMeasurePreserving_id_apply F)
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2Advanced finish the forward-backward Lp composition with the identity lemma",
    )
    changed |= did

    old = """    simpa only [Function.comp_def, chart.coord.symm_apply_apply,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
"""
    new = """    exact hcomp.symm.trans (Lp.compMeasurePreserving_id_apply u)
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2Advanced finish the backward-forward Lp composition with the identity lemma",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  rw [ModularGroup.im_smul_eq_div_normSq]
  change (((3 : ℝ) * 3 + (4 : ℝ) * 4)⁻¹) = (1 : ℝ) / 25
  norm_num
"""
    new = """  rw [ModularGroup.im_smul_eq_div_normSq]
  norm_num [gammaTwoHyperbolic, UpperHalfPlane.I, UpperHalfPlane.denom,
    Matrix.SpecialLinearGroup.map, Matrix.SpecialLinearGroup.toGL,
    Complex.normSq]
"""
    text, did = replace_exact(
        text, old, new, 1,
        "FunctionalAnalysis unfold the concrete special-linear matrix action",
    )
    changed |= did

    old = """  simpa [UpperHalfPlane.σ, MulAction.compHom_smul_def] using
    (UpperHalfPlane.denom_cocycle_σ
      ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) z)
"""
    new = """  simpa [UpperHalfPlane.σ, MulAction.compHom_smul_def,
    Matrix.SpecialLinearGroup.mapGL] using
    (UpperHalfPlane.denom_cocycle_σ
      ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) z)
"""
    text, did = replace_exact(
        text, old, new, 1,
        "FunctionalAnalysis unfold the subgroup mapGL action in the denominator cocycle",
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
