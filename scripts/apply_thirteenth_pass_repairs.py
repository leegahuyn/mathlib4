from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied/source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def repair_spt2() -> None:
    path = ROOT / "Spt2.lean"
    text = path.read_text(encoding="utf-8")
    old = """  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  unfold principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply]
  change Algebra.Extension.Cotangent.of
      (quotientSpanCotangentEquivKer f
        (principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a))) =
    Algebra.Extension.Cotangent.mk
      (P := quotientExtension f)
      ⟨a * f, by
        rw [quotientExtension_ker]
        exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩
  rw [hmap]
  apply Algebra.Extension.Cotangent.ext
  simp [quotientSpanCotangentEquivKer, quotientExtension_ker,
    Algebra.Extension.Cotangent.val_mk, Algebra.Extension.Cotangent.val_of]
"""
    new = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  change Algebra.Extension.Cotangent.of
      (quotientSpanCotangentEquivKer f
        (principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a))) =
    Algebra.Extension.Cotangent.mk
      (P := quotientExtension f)
      ⟨a * f, by
        rw [quotientExtension_ker]
        exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩
  rw [hprincipal, hmap]
  apply Algebra.Extension.Cotangent.ext
  simp [quotientSpanCotangentEquivKer, quotientExtension_ker,
    Algebra.Extension.Cotangent.val_mk, Algebra.Extension.Cotangent.val_of]
"""
    text, changed = replace_once(text, old, new,
        "Spt2 rewrite principal equivalence only after target normalization")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1() -> None:
    path = ROOT / "Mock1.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem A_inftyMatrix_mulVec_eq_A_infty_mul (c : S4Col → ℚ) :
    A_inftyMatrix.mulVec c = A_infty_mul c := by
  classical
  funext i
  simp [Matrix.mulVec, A_inftyMatrix, A_infty, A_infty_mul]
"""
    new = """theorem A_inftyMatrix_mulVec_eq_A_infty_mul (c : S4Col → ℚ) :
    A_inftyMatrix.mulVec c = A_infty_mul c := by
  classical
  funext i
  simp [Matrix.mulVec, dotProduct, A_inftyMatrix, A_infty, A_infty_mul,
    sub_eq_add_neg]
"""
    text, did = replace_once(text, old, new,
        "Mock1 unfold and normalize the Sum-indexed extraction dot product")
    changed |= did

    old = """theorem S4D6J12Matrix_mulVec_solution :
    S4D6J12Matrix.mulVec S4D6J12Solution = S4D6J12Target := by
  ext i
  fin_cases i <;> decide
"""
    new = """theorem S4D6J12Matrix_mulVec_solution :
    S4D6J12Matrix.mulVec S4D6J12Solution = S4D6J12Target := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      S4D6J12Matrix, S4D6J12MatrixEntry,
      S4D6J12Solution, S4D6J12SolutionEntry, S4D6J12Target]
"""
    text, did = replace_once(text, old, new,
        "Mock1 expand the closed D6/J12 matrix product")
    changed |= did

    old = """theorem S4D6J12Solution_coeff_sum :
    (∑ j : Fin S4J12, S4D6J12Solution j) = 1 := by
  decide
"""
    new = """theorem S4D6J12Solution_coeff_sum :
    (∑ j : Fin S4J12, S4D6J12Solution j) = 1 := by
  norm_num [Fin.sum_univ_succ, S4D6J12Solution, S4D6J12SolutionEntry]
"""
    text, did = replace_once(text, old, new,
        "Mock1 expand the closed D6/J12 coefficient sum")
    changed |= did

    old = """theorem S4D6J12Matrix_mulVec_solve (b : Fin S4D6 → ℚ) :
    S4D6J12Matrix.mulVec (S4D6J12Solve b) = b := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, S4D6J12Matrix, S4D6J12MatrixEntry, S4D6J12Solve] <;>
      ring
"""
    new = """theorem S4D6J12Matrix_mulVec_solve (b : Fin S4D6 → ℚ) :
    S4D6J12Matrix.mulVec (S4D6J12Solve b) = b := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      S4D6J12Matrix, S4D6J12MatrixEntry, S4D6J12Solve] <;>
    try ring
  all_goals
    exact congrArg b (Fin.ext rfl)
"""
    text, did = replace_once(text, old, new,
        "Mock1 close symbolic D6/J12 Fin proof irrelevance")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_spt2()
    repair_mock1()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
