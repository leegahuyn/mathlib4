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

    old_defs = """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
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
    new_defs = """noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    (((Ideal.Cotangent.equivOfEq
        (Ideal.span ({f} : Set K[X])) (quotientExtension f).ker
        (quotientExtension_ker f).symm).restrictScalars K).trans
      (quotientExtensionCotangentEquivKer f))
"""
    text, did = replace_once(text, old_defs, new_defs,
        "Spt2 replace dependent cotangent transport with equivOfEq")
    changed |= did

    old_proof = """  have hker : (quotientExtension f).ker = Ideal.span ({f} : Set K[X]) :=
    quotientExtension_ker f
  cases hker
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  unfold quotientSpanCotangentEquivKer principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply, hmap]
  rfl
"""
    new_proof = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  rw [hprincipal, hmap, Ideal.Cotangent.equivOfEq_toCotangent]
  rfl
"""
    text, did = replace_once(text, old_proof, new_proof,
        "Spt2 prove transported conormal generator directly")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1() -> None:
    path = ROOT / "Mock1.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  · intro h n
    exact (lcmIdealCondition_iff_dvd M pk (x n - y n)).mpr
      (Int.natCast_dvd_natCast.mpr
        (Nat.lcm_dvd (Int.natCast_dvd_natCast.mp (h.1 n))
          (Int.natCast_dvd_natCast.mp (h.2 n))))
"""
    new = """  · intro h n
    apply (lcmIdealCondition_iff_dvd M pk (x n - y n)).mpr
    change lcm (M : ℤ) (pk : ℤ) ∣ x n - y n
    exact lcm_dvd (h.1 n) (h.2 n)
"""
    text, did = replace_once(text, old, new,
        "Mock1 combine integer divisibility through lcm")
    changed |= did

    old = """theorem thetaKernelL1PassingTable_passes :
    PassesPaperPredictionTailTable thetaKernelL1PassingTableRow := by
  intro row
  exact (thetaKernelL1PassingTableRow row).residual_abs_le_tailBound_of_pass rfl
"""
    new = """theorem thetaKernelL1PassingTable_passes :
    PassesPaperPredictionTailTable thetaKernelL1PassingTableRow := by
  intro row
  fin_cases row <;>
    exact (thetaKernelL1PassingTableRow _).residual_abs_le_tailBound_of_pass rfl
"""
    text, did = replace_once(text, old, new,
        "Mock1 discharge each passing-table row concretely")
    changed |= did

    old = """inductive PaperT5RegressionCertRow where
  | intercept
  | slopeProbe
deriving DecidableEq, Fintype, Repr
"""
    new = """inductive PaperT5RegressionCertRow where
  | intercept
  | slopeProbe
deriving DecidableEq, Repr

instance : Fintype PaperT5RegressionCertRow where
  elems := {PaperT5RegressionCertRow.intercept,
    PaperT5RegressionCertRow.slopeProbe}
  complete row := by
    cases row <;> simp
"""
    text, did = replace_once(text, old, new,
        "Mock1 provide explicit two-row Fintype instance")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_spt2()
    repair_mock1()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
