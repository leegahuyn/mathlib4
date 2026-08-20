from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")


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


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    old = """theorem reference_paper_tables_f_checklist :
    (forall r, List.Mem r referencePaperTablesFCompletionCertificate.requirements) /\
      referencePaperTablesFCompletionCertificate.paperTables.parameterTable.rows.length = 11 /\
      referencePaperTablesFCompletionCertificate.paperTables.residualTable.rows.length = 16 /\
      referencePaperTablesFCompletionCertificate.paperTables.externalScript.rows.length = 16 /\
      (referencePaperTablesFCompletionCertificate.paperTables.residualTable.threshold.lower = 0 /\
        referencePaperTablesFCompletionCertificate.paperTables.residualTable.threshold.upper = 5) /\
      (forall row,
        List.Mem row referencePaperTablesFCompletionCertificate.paperTables.parameterTable.rows ->
          row.mode = TableRowMode.theoremBacked /\
            TableRowMode.toPaperLabelKind row.mode = PaperLabelKind.theorem /\
              row.alphaInterval.Contains row.alpha) /\
      (forall row,
        List.Mem row referencePaperTablesFCompletionCertificate.paperTables.residualTable.rows ->
          row.mode = TableRowMode.diagnosticOnly /\
            TableRowMode.toPaperLabelKind row.mode = PaperLabelKind.diagnosticOnly /\
              row.rtCheck.valueInterval.Contains row.rtCheck.value /\
                row.rsCheck.valueInterval.Contains row.rsCheck.value /\
                  row.rtCheck.valueInterval.upper <= row.rtCheck.threshold.upper /\
                    row.rsCheck.valueInterval.upper <= row.rsCheck.threshold.upper) /\
      (forall row,
        List.Mem row referencePaperTablesFCompletionCertificate.paperTables.externalScript.rows ->
          row.rtCheck.pass = true /\ row.rsCheck.pass = true) /\
      referencePaperTablesFCompletionCertificate.paperTables.parameterTable.rows =
        referencePaperTablesFCompletionCertificate.parameterRows /\
      referencePaperTablesFCompletionCertificate.paperTables.residualTable.rows =
        referencePaperTablesFCompletionCertificate.residualRows /\
      referencePaperTablesFCompletionCertificate.paperTables.externalScript.rows =
        referencePaperTablesFCompletionCertificate.residualRows :=
  And.intro
    (fun r => referencePaperTablesFCompletionCertificate.covers_at r)
    (And.intro
      referencePaperTablesFCompletionCertificate.parameter_schema_length_at
      (And.intro
        referencePaperTablesFCompletionCertificate.residual_schema_length_at
        (And.intro
          referencePaperTablesFCompletionCertificate.external_rows_length_at
          (And.intro
            referencePaperTablesFCompletionCertificate.threshold_bounds_at
            (And.intro
              (fun row hrow =>
                And.intro
                  (referencePaperTablesFCompletionCertificate.parameter_row_mode_at row hrow)
                  (And.intro
                    (referencePaperTablesFCompletionCertificate.parameter_row_kind_at row hrow)
                    (referencePaperTablesFCompletionCertificate.parameter_row_alpha_mem_at row hrow)))
              (And.intro
                (fun row hrow =>
                  And.intro
                    (referencePaperTablesFCompletionCertificate.residual_row_mode_at row hrow)
                    (And.intro
                      (referencePaperTablesFCompletionCertificate.residual_row_kind_at row hrow)
                      (And.intro
                        (referencePaperTablesFCompletionCertificate.residual_rt_value_mem_at row hrow)
                        (And.intro
                          (referencePaperTablesFCompletionCertificate.residual_rs_value_mem_at row hrow)
                          (And.intro
                            (referencePaperTablesFCompletionCertificate.residual_rt_threshold_at row hrow)
                            (referencePaperTablesFCompletionCertificate.residual_rs_threshold_at row hrow)))))
                (And.intro
                  (fun row hrow =>
                    referencePaperTablesFCompletionCertificate.external_row_rechecked_at row hrow)
                  (And.intro
                    referencePaperTablesFCompletionCertificate.parameter_rows_into_cert_at
                    (And.intro
                      referencePaperTablesFCompletionCertificate.residual_rows_into_cert_at
                      referencePaperTablesFCompletionCertificate.external_rows_into_cert_at))))))))))
"""
    new = """theorem reference_paper_tables_f_checklist :
    (forall r, List.Mem r referencePaperTablesFCompletionCertificate.requirements) /\
      referencePaperTablesFCompletionCertificate.paperTables.parameterTable.rows.length = 11 /\
      referencePaperTablesFCompletionCertificate.paperTables.residualTable.rows.length = 16 /\
      referencePaperTablesFCompletionCertificate.paperTables.externalScript.rows.length = 16 /\
      (referencePaperTablesFCompletionCertificate.paperTables.residualTable.threshold.lower = 0 /\
        referencePaperTablesFCompletionCertificate.paperTables.residualTable.threshold.upper = 5) /\
      (forall row,
        List.Mem row referencePaperTablesFCompletionCertificate.paperTables.parameterTable.rows ->
          row.mode = TableRowMode.theoremBacked /\
            TableRowMode.toPaperLabelKind row.mode = PaperLabelKind.theorem /\
              row.alphaInterval.Contains row.alpha) /\
      (forall row,
        List.Mem row referencePaperTablesFCompletionCertificate.paperTables.residualTable.rows ->
          row.mode = TableRowMode.diagnosticOnly /\
            TableRowMode.toPaperLabelKind row.mode = PaperLabelKind.diagnosticOnly /\
              row.rtCheck.valueInterval.Contains row.rtCheck.value /\
                row.rsCheck.valueInterval.Contains row.rsCheck.value /\
                  row.rtCheck.valueInterval.upper <= row.rtCheck.threshold.upper /\
                    row.rsCheck.valueInterval.upper <= row.rsCheck.threshold.upper) /\
      (forall row,
        List.Mem row referencePaperTablesFCompletionCertificate.paperTables.externalScript.rows ->
          row.rtCheck.pass = true /\ row.rsCheck.pass = true) /\
      referencePaperTablesFCompletionCertificate.paperTables.parameterTable.rows =
        referencePaperTablesFCompletionCertificate.parameterRows /\
      referencePaperTablesFCompletionCertificate.paperTables.residualTable.rows =
        referencePaperTablesFCompletionCertificate.residualRows /\
      referencePaperTablesFCompletionCertificate.paperTables.externalScript.rows =
        referencePaperTablesFCompletionCertificate.residualRows := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun r => referencePaperTablesFCompletionCertificate.covers_at r
  · exact referencePaperTablesFCompletionCertificate.parameter_schema_length_at
  · exact referencePaperTablesFCompletionCertificate.residual_schema_length_at
  · exact referencePaperTablesFCompletionCertificate.external_rows_length_at
  · exact referencePaperTablesFCompletionCertificate.threshold_bounds_at
  · intro row hrow
    exact ⟨referencePaperTablesFCompletionCertificate.parameter_row_mode_at row hrow,
      referencePaperTablesFCompletionCertificate.parameter_row_kind_at row hrow,
      referencePaperTablesFCompletionCertificate.parameter_row_alpha_mem_at row hrow⟩
  · intro row hrow
    exact ⟨referencePaperTablesFCompletionCertificate.residual_row_mode_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_row_kind_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_rt_value_mem_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_rs_value_mem_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_rt_threshold_at row hrow,
      referencePaperTablesFCompletionCertificate.residual_rs_threshold_at row hrow⟩
  · intro row hrow
    exact referencePaperTablesFCompletionCertificate.external_row_rechecked_at row hrow
  · exact referencePaperTablesFCompletionCertificate.parameter_rows_into_cert_at
  · exact referencePaperTablesFCompletionCertificate.residual_rows_into_cert_at
  · exact referencePaperTablesFCompletionCertificate.external_rows_into_cert_at
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced rebuild the paper-table checklist propositionally")
    changed |= did

    old = """  all_rows_certified := by
    intro row hrow
    simp [referenceOLSRows] at hrow
    rcases hrow with h | h | h | h | h
    · subst row
"""
    new = """  all_rows_certified := by
    intro row hrow
    simp only [referenceOLSRows, List.mem_cons, List.mem_singleton] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl
    ·
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced split the five concrete OLS rows by equality")
    changed |= did

    constructors = [
        "rademacherAlphaExtractionBoundary", "tailDominanceRationalInequality",
        "degeneracyCoefficientChannel", "cardyConstantConvention",
        "rationalOlsIntervalTable", "growthStabilitySptPadicCompletion",
        "actualEntropyAlphaExtractionValues", "actualDegeneracyChannelInstance",
        "actualRationalOlsIntervalTable", "finalAlphaCeffIntervals",
    ]
    cases = []
    for depth, ctor in enumerate(constructors):
        proof = "List.Mem.head _"
        for _ in range(depth):
            proof = f"List.Mem.tail _ ({proof})"
        cases.append(f"  | {ctor} => exact {proof}")
    old = """theorem mem_all (r : EntropyCardyGRequirement) :
    List.Mem r all := by
  cases r <;> simp [all]
"""
    new = """theorem mem_all (r : EntropyCardyGRequirement) :
    List.Mem r all := by
  cases r with
""" + "\n".join(cases) + "\n"
    text, did = replace_once(text, old, new,
        "Mock1Advanced prove the ten entropy/Cardy requirements structurally")
    changed |= did

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
