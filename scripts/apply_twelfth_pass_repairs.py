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
    changed = False

    direct_defs = """noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    (((Ideal.Cotangent.equivOfEq
        (Ideal.span ({f} : Set K[X])) (quotientExtension f).ker
        (quotientExtension_ker f).symm).restrictScalars K).trans
      (quotientExtensionCotangentEquivKer f))
"""
    helper_defs = """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]
  exact LinearEquiv.refl K _

noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    ((quotientSpanCotangentEquivKer f).trans
      (quotientExtensionCotangentEquivKer f))
"""
    text, did = replace_once(text, direct_defs, helper_defs,
        "Spt2 restore instance-safe cotangent helper")
    changed |= did

    direct_proof = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  rw [hprincipal, hmap, Ideal.Cotangent.equivOfEq_toCotangent]
  rfl
"""
    helper_proof = """  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
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
    text, did = replace_once(text, direct_proof, helper_proof,
        "Spt2 unfold principal equivalence before generator rewrite")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1() -> None:
    path = ROOT / "Mock1.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem S4D6J12Matrix_mulVec_solution :
    S4D6J12Matrix.mulVec S4D6J12Solution = S4D6J12Target := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, S4D6J12Matrix, S4D6J12MatrixEntry,
      S4D6J12Solution, S4D6J12SolutionEntry, S4D6J12Target]
"""
    new = """theorem S4D6J12Matrix_mulVec_solution :
    S4D6J12Matrix.mulVec S4D6J12Solution = S4D6J12Target := by
  ext i
  fin_cases i <;> decide
"""
    text, did = replace_once(text, old, new,
        "Mock1 decide the closed D6/J12 matrix product")
    changed |= did

    old = """theorem S4D6J12Solution_coeff_sum :
    (∑ j : Fin S4J12, S4D6J12Solution j) = 1 := by
  norm_num [S4D6J12Solution, S4D6J12SolutionEntry]
"""
    new = """theorem S4D6J12Solution_coeff_sum :
    (∑ j : Fin S4J12, S4D6J12Solution j) = 1 := by
  decide
"""
    text, did = replace_once(text, old, new,
        "Mock1 decide the closed D6/J12 coefficient sum")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_spt2()
    repair_mock1()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
