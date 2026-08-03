from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(path: Path, old: str, new: str, label: str) -> bool:
    text = path.read_text(encoding="utf-8")
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied or source changed")
        return False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    path.write_text(text.replace(old, new), encoding="utf-8", newline="\n")
    print(f"{label}: applied")
    return True


def main() -> int:
    changed = False

    spt2 = ROOT / "Spt2.lean"
    changed = replace_once(
        spt2,
        """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
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
""",
        """noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    (((Ideal.cotangentEquivOfEq (quotientExtension_ker f).symm).restrictScalars K).trans
      (quotientExtensionCotangentEquivKer f))
""",
        "Spt2 restore direct ideal-cotangent transport",
    ) or changed

    changed = replace_once(
        spt2,
        """  ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  unfold principalCotangentQuotEquiv quotientExtensionCotangentEquivKer
  rw [LinearEquiv.ofBijective_apply, hmap]
  simp [quotientSpanCotangentEquivKer, quotientExtension_ker,
    Algebra.Extension.Cotangent.val_mk, Algebra.Extension.Cotangent.val_of]
""",
        """  ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  unfold principalCotangentQuotEquiv quotientExtensionCotangentEquivKer
  change (Algebra.Extension.Cotangent.of
      ((Ideal.cotangentEquivOfEq (quotientExtension_ker f).symm)
        ((principalCotangentQuotMap f)
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a)))).val =
    (Algebra.Extension.Cotangent.mk
      (P := quotientExtension f)
      ⟨a * f, by
        rw [quotientExtension_ker]
        exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩).val
  rw [hmap]
  simp [Algebra.Extension.Cotangent.val_mk, Algebra.Extension.Cotangent.val_of]
  rfl
""",
        "Spt2 compute transported cotangent generator explicitly",
    ) or changed

    spt4 = ROOT / "Spt4.lean"
    changed = replace_once(
        spt4,
        """theorem resC_d_succ_zero (N j : ℕ) : (resC N).d (j + 1 + 1) (j + 1) = 0 := by
  simpa [resC, df] using
    (ChainComplex.of_d Xf (df N)
      (fun n => by
        have : df N (n + 1) = 0 := rfl
        rw [this, zero_comp]) (j + 1))
""",
        """theorem resC_d_succ_zero (N j : ℕ) : (resC N).d (j + 1 + 1) (j + 1) = 0 := by
  change ChainComplex.of.d Xf (df N) (j + 1 + 1) (j + 1) = 0
  rw [ChainComplex.of_d]
  rfl
""",
        "Spt4 compute higher differential definitionally",
    ) or changed

    print("Terminal SPT repairs changed sources." if changed else "No terminal SPT changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
