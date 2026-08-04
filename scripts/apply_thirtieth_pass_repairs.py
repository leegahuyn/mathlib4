from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old_start = """theorem reference_paper_tables_f_checklist :
    (forall r, List.Mem r referencePaperTablesFCompletionCertificate.requirements) /\\
      referencePaperTablesFCompletionCertificate.paperTables.parameterTable.rows.length = 11 /\\
      referencePaperTablesFCompletionCertificate.paperTables.residualTable.rows.length = 16 /\\
      referencePaperTablesFCompletionCertificate.paperTables.externalScript.rows.length = 16 /\\
      (referencePaperTablesFCompletionCertificate.paperTables.residualTable.threshold.lower = 0 /\\
        referencePaperTablesFCompletionCertificate.paperTables.residualTable.threshold.upper = 5) /\\
      (forall row,
        List.Mem row referencePaperTablesFCompletionCertificate.paperTables.parameterTable.rows ->
          row.mode = TableRowMode.theoremBacked /\\
            TableRowMode.toPaperLabelKind row.mode = PaperLabelKind.theorem /\\
              row.alphaInterval.Contains row.alpha) /\\
      (forall row,
        List.Mem row referencePaperTablesFCompletionCertificate.paperTables.residualTable.rows ->
          row.mode = TableRowMode.diagnosticOnly /\\
            TableRowMode.toPaperLabelKind row.mode = PaperLabelKind.diagnosticOnly /\\
              row.rtCheck.valueInterval.Contains row.rtCheck.value /\\
                row.rsCheck.valueInterval.Contains row.rsCheck.value /\\
                  row.rtCheck.valueInterval.upper <= row.rtCheck.threshold.upper /\\
                    row.rsCheck.valueInterval.upper <= row.rsCheck.threshold.upper) /\\
      (forall row,
        List.Mem row referencePaperTablesFCompletionCertificate.paperTables.externalScript.rows ->
          row.rtCheck.pass = true /\\ row.rsCheck.pass = true) /\\
      referencePaperTablesFCompletionCertificate.paperTables.parameterTable.rows =
        referencePaperTablesFCompletionCertificate.parameterRows /\\
      referencePaperTablesFCompletionCertificate.paperTables.residualTable.rows =
        referencePaperTablesFCompletionCertificate.residualRows /\\
      referencePaperTablesFCompletionCertificate.paperTables.externalScript.rows =
        referencePaperTablesFCompletionCertificate.residualRows :=
"""
    start = text.find(old_start)
    if start >= 0:
        end = text.find("\n\n/-!\nMathematical content for definitional equalities.", start)
        if end < 0:
            raise RuntimeError("Mock1Advanced checklist end anchor not found")
        statement = old_start
        proof = """by
  refine ⟨
    (fun r => referencePaperTablesFCompletionCertificate.covers_at r),
    referencePaperTablesFCompletionCertificate.parameter_schema_length_at,
    referencePaperTablesFCompletionCertificate.residual_schema_length_at,
    referencePaperTablesFCompletionCertificate.external_rows_length_at,
    referencePaperTablesFCompletionCertificate.threshold_bounds_at,
    ?_, ?_, ?_,
    referencePaperTablesFCompletionCertificate.parameter_rows_into_cert_at,
    referencePaperTablesFCompletionCertificate.residual_rows_into_cert_at,
    referencePaperTablesFCompletionCertificate.external_rows_into_cert_at⟩
  · intro row hrow
    exact ⟨
      referencePaperTablesFCompletionCertificate.parameter_row_mode_at row hrow,
      referencePaperTablesFCompletionCertificate.parameter_row_kind_at row hrow,
      referencePaperTablesFCompletionCertificate.parameter_row_alpha_mem_at row hrow⟩
  · intro row hrow
    exact ⟨
      referencePaperTablesFCompletionCertificate.residual_row_mode_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_row_kind_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_rt_value_mem_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_rs_value_mem_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_rt_threshold_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_rs_threshold_at row hrow⟩
  · intro row hrow
    exact referencePaperTablesFCompletionCertificate.external_row_rechecked_at row hrow
"""
        text = text[:start] + statement + proof + text[end:]
        changed = True
        print("Mock1Advanced rebuild the paper-table checklist with structured conjunctions: applied")
    elif "Mock1Advanced checklist proof marker" not in text:
        print("Mock1Advanced paper-table checklist: source changed; skipped")

    old = """  all_rows_certified := by
    intro row hrow
    simp only [referenceOLSRows, List.mem_cons, List.mem_singleton] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl
    ·
      exact ⟨referenceAlphaOLSRow.table_number_at,
        referenceAlphaOLSRow.estimate_mem_at,
        referenceAlphaOLSRow.mode_diagnostic_at⟩
    · subst row
      exact ⟨referenceBetaOLSRow.table_number_at,
        referenceBetaOLSRow.estimate_mem_at,
        referenceBetaOLSRow.mode_diagnostic_at⟩
    · subst row
      exact ⟨referenceGammaOLSRow.table_number_at,
        referenceGammaOLSRow.estimate_mem_at,
        referenceGammaOLSRow.mode_diagnostic_at⟩
    · subst row
      exact ⟨referenceCeffOLSRow.table_number_at,
        referenceCeffOLSRow.estimate_mem_at,
        referenceCeffOLSRow.mode_diagnostic_at⟩
    · subst row
      exact ⟨referenceRSSOLSRow.table_number_at,
        referenceRSSOLSRow.estimate_mem_at,
        referenceRSSOLSRow.mode_diagnostic_at⟩
"""
    new = """  all_rows_certified := by
    intro row hrow
    simp only [referenceOLSRows, List.mem_cons, List.mem_singleton] at hrow
    rcases hrow with hα | hrest
    · subst row
      exact ⟨referenceAlphaOLSRow.table_number_at,
        referenceAlphaOLSRow.estimate_mem_at,
        referenceAlphaOLSRow.mode_diagnostic_at⟩
    rcases hrest with hβ | hrest
    · subst row
      exact ⟨referenceBetaOLSRow.table_number_at,
        referenceBetaOLSRow.estimate_mem_at,
        referenceBetaOLSRow.mode_diagnostic_at⟩
    rcases hrest with hγ | hrest
    · subst row
      exact ⟨referenceGammaOLSRow.table_number_at,
        referenceGammaOLSRow.estimate_mem_at,
        referenceGammaOLSRow.mode_diagnostic_at⟩
    rcases hrest with hc | hrss
    · subst row
      exact ⟨referenceCeffOLSRow.table_number_at,
        referenceCeffOLSRow.estimate_mem_at,
        referenceCeffOLSRow.mode_diagnostic_at⟩
    · subst row
      exact ⟨referenceRSSOLSRow.table_number_at,
        referenceRSSOLSRow.estimate_mem_at,
        referenceRSSOLSRow.mode_diagnostic_at⟩
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced split OLS rows without chained rfl patterns")
    changed |= did

    old = """  profile_negative := by
    intro p hp
    simp [referenceT1PolarProfile] at hp
    subst p
    decide
"""
    new = """  profile_negative := by
    intro p hp
    have hp' : p = ((-1 : ℤ), (1 : ℚ)) := by
      simpa [referenceT1PolarProfile] using hp
    subst p
    norm_num
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced identify the T1 polar profile explicitly")
    changed |= did

    old = """  profile_negative := by
    intro p hp
    simp [referenceT2PolarProfile] at hp
    rcases hp with hp | hp <;> subst p <;> decide
"""
    new = """  profile_negative := by
    intro p hp
    have hp' : p = ((-2 : ℤ), (1 : ℚ)) ∨
        p = ((-1 : ℤ), (1 : ℚ)) := by
      simpa [referenceT2PolarProfile] using hp
    rcases hp' with rfl | rfl <;> norm_num
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced identify the T2 polar profile explicitly")
    changed |= did

    text, did = replace_once(text,
        """theorem reference_t1_matvec_eq_rhs :
    MatVecRat referenceT1Matrix referenceT1Solution = referenceT1RHS := by
  decide
""",
        """theorem reference_t1_matvec_eq_rhs :
    MatVecRat referenceT1Matrix referenceT1Solution = referenceT1RHS := by
  norm_num [MatVecRat, dotRat, referenceT1Matrix,
    referenceT1Solution, referenceT1RHS]
""",
        "Mock1Advanced compute the T1 rational matrix product")
    changed |= did

    text, did = replace_once(text,
        """theorem reference_t2_matvec_eq_rhs :
    MatVecRat referenceT2Matrix referenceT2Solution = referenceT2RHS := by
  decide
""",
        """theorem reference_t2_matvec_eq_rhs :
    MatVecRat referenceT2Matrix referenceT2Solution = referenceT2RHS := by
  norm_num [MatVecRat, dotRat, referenceT2Matrix,
    referenceT2Solution, referenceT2RHS]
""",
        "Mock1Advanced compute the T2 rational matrix product")
    changed |= did

    old_start = "def referenceT1ConcreteCertificate : ConcreteCertificate Unit where\n"
    start = text.find(old_start)
    if start >= 0:
        end = text.find("\n\ndef referenceT2ConcreteCertificate", start)
        if end < 0:
            raise RuntimeError("Mock1Advanced T1 certificate end anchor not found")
        repl = """noncomputable def referenceT1ConcreteCertificate : ConcreteCertificate Unit :=
  { referenceConcreteCertificate with
    principalPart := referenceT1PrincipalPart
    paperPrincipalPartRows := referenceT1PrincipalPart.order
    paperPrincipalPartRows_eq := rfl }
"""
        text = text[:start] + repl + text[end:]
        changed = True
        print("Mock1Advanced update the T1 certificate from the complete reference record: applied")

    old_start = "def referenceT2ConcreteCertificate : ConcreteCertificate Unit where\n"
    start = text.find(old_start)
    if start >= 0:
        end = text.find("\n\ndef referenceT1AssemblyCertificate", start)
        if end < 0:
            raise RuntimeError("Mock1Advanced T2 certificate end anchor not found")
        repl = """noncomputable def referenceT2ConcreteCertificate : ConcreteCertificate Unit :=
  { referenceConcreteCertificate with
    principalPart := referenceT2PrincipalPart
    paperPrincipalPartRows := referenceT2PrincipalPart.order
    paperPrincipalPartRows_eq := rfl }
"""
        text = text[:start] + repl + text[end:]
        changed = True
        print("Mock1Advanced update the T2 certificate from the complete reference record: applied")

    for name in [
        "referenceT1AbstractVerification", "referenceT2AbstractVerification",
        "referenceCuspTransportFamilyCert", "referenceOtherCuspTransportFamily",
    ]:
        old = f"def {name}"
        new = f"noncomputable def {name}"
        if old in text and new not in text:
            text = text.replace(old, new, 1)
            changed = True
            print(f"Mock1Advanced mark {name} noncomputable: applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_once(text,
        """theorem powerShiftIntegerHom_modulus_eq_zero (M p k : ℕ) :
    powerShiftIntegerHom M p k
      (p ^ thicknessExponent M p k : ℤ) = 0 := by
  change (p ^ shiftExponent M p k : ZMod (Pk p k)) *
      (p ^ thicknessExponent M p k : ZMod (Pk p k)) = 0
  rw [← Nat.cast_mul, pow_shift_mul_pow_thickness]
  exact ZMod.natCast_self (Pk p k)
""",
        """theorem powerShiftIntegerHom_modulus_eq_zero (M p k : ℕ) :
    powerShiftIntegerHom M p k
      (p ^ thicknessExponent M p k : ℤ) = 0 := by
  rw [powerShiftIntegerHom_apply]
  rw [← Nat.cast_mul, pow_shift_mul_pow_thickness]
  exact ZMod.natCast_self (Pk p k)
""",
        "Mock2 expose the power-shift integer hom before modulus reduction")
    changed |= did

    text, did = replace_once(text,
        """@[simp] theorem powerShiftHom_intCast
    (M p k : ℕ) (z : ℤ) :
    powerShiftHom M p k
        (z : ZMod (p ^ thicknessExponent M p k)) =
      (p ^ shiftExponent M p k : ZMod (Pk p k)) *
        (z : ZMod (Pk p k)) := by
  simp [powerShiftHom]
""",
        """@[simp] theorem powerShiftHom_intCast
    (M p k : ℕ) (z : ℤ) :
    powerShiftHom M p k
        (z : ZMod (p ^ thicknessExponent M p k)) =
      (p ^ shiftExponent M p k : ZMod (Pk p k)) *
        (z : ZMod (Pk p k)) := by
  change powerShiftIntegerHom M p k z = _
  exact powerShiftIntegerHom_apply M p k z
""",
        "Mock2 compute the lifted power-shift map on integer representatives")
    changed |= did

    text, did = replace_once(text,
        """  calc
    M * p ^ shiftExponent M p k =
        (p ^ thicknessExponent M p k * c) *
          p ^ shiftExponent M p k := by rw [hc]
""",
        """  calc
    M * p ^ shiftExponent M p k =
        (p ^ thicknessExponent M p k * c) *
          p ^ shiftExponent M p k :=
      congrArg (fun t => t * p ^ shiftExponent M p k) hc
""",
        "Mock2 preserve the original modulus inside the shift exponent")
    changed |= did

    text, did = replace_once(text,
        """  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simpa using map_add (powerShiftHom M p k) x y
""",
        """  map_zero' := by
    apply Subtype.ext
    exact map_zero (powerShiftHom M p k)
  map_add' x y := by
    apply Subtype.ext
    change powerShiftHom M p k (x + y) =
      powerShiftHom M p k x + powerShiftHom M p k y
    exact map_add (powerShiftHom M p k) x y
""",
        "Mock2 inherit power-shift kernel homomorphism laws directly")
    changed |= did

    text, did = replace_once(text,
        """      (p ^ shiftExponent M p k : ZMod (Pk p k)) *
        (z : ZMod (Pk p k)) := by
  simp
""",
        """      (p ^ shiftExponent M p k : ZMod (Pk p k)) *
        (z : ZMod (Pk p k)) := by
  exact powerShiftHom_intCast M p k z
""",
        "Mock2 reuse the power-shift representative formula in the kernel")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) := by
"""
    new = """      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        (↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) : ℝ≥0∞) := by
"""
    text, changed = replace_once(text, old, new,
        "Mock2Advanced specify the ENNReal codomain of the hyperbolic density")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """              rw [hr, map_smulₛₗ]
              change r * (F v).re - 0 * (F v).im = r * (F v).re
              ring }
"""
    new = """              rw [hr, map_smulₛₗ]
              simpa only [starRingEnd_apply, Complex.star_def,
                Complex.conj_ofReal, smul_eq_mul, Complex.mul_re,
                Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] }
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis normalize real scalar anti-linearity directly")
    changed |= did

    old = """            rw [hr, map_smulₛₗ]
            change r * (B u v).re - 0 * (B u v).im = r * (B u v).re
            ring)
"""
    new = """            rw [hr, map_smulₛₗ]
            simpa only [starRingEnd_apply, Complex.star_def,
              Complex.conj_ofReal, smul_eq_mul, Complex.mul_re,
              Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero])
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis normalize form anti-linearity directly")
    changed |= did

    text, did = replace_once(text,
        """      have hstar : starRingEnd ℂ Complex.I = -Complex.I := by
        ext <;> norm_num [starRingEnd_apply, Complex.star_def]
""",
        """      have hstar : starRingEnd ℂ Complex.I = -Complex.I := by
        simpa only [starRingEnd_apply, Complex.star_def] using Complex.conj_I
""",
        "FunctionalAnalysis use the canonical conjugation identity for I")
    changed |= did

    text, did = replace_once(text,
        """theorem solve_spec
    (d : FredholmBypassData A) (F : W) :
    A (d.solve F) = F := by
  simpa [solve, solutionOperator] using
    d.unshiftedEquiv.apply_symm_apply F
""",
        """theorem solve_spec
    (d : FredholmBypassData A) (F : W) :
    A (d.solve F) = F := by
  change d.unshiftedEquiv (d.unshiftedEquiv.symm F) = F
  exact d.unshiftedEquiv.apply_symm_apply F
""",
        "FunctionalAnalysis expose the unshifted equivalence in solve_spec")
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
