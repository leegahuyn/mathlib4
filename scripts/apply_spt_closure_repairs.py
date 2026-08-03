from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(path: Path, old: str, new: str, label: str) -> bool:
    text = path.read_text(encoding="utf-8")
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied/source changed")
        return False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    path.write_text(text.replace(old, new), encoding="utf-8", newline="\n")
    print(f"{label}: applied")
    return True


def main() -> int:
    changed = False
    spt2 = ROOT / "Spt2.lean"

    changed |= replace_once(
        spt2,
        """noncomputable def quotientExtensionCotangentEquivKer (f : K[X]) :
    (quotientExtension f).ker.Cotangent ≃ₗ[K] (quotientExtension f).Cotangent where
  toFun x := Algebra.Extension.Cotangent.of x
  invFun x := Algebra.Extension.Cotangent.val x
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := by
    apply Algebra.Extension.Cotangent.ext
    rfl
  map_smul' r x := by
    ext
    simp [Algebra.Extension.Cotangent.val_smul'']
""",
        """noncomputable def quotientExtensionCotangentEquivKer (f : K[X]) :
    (quotientExtension f).ker.Cotangent ≃ₗ[K] (quotientExtension f).Cotangent where
  toFun x := Algebra.Extension.Cotangent.of x
  invFun x := Algebra.Extension.Cotangent.val x
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := by
    apply Algebra.Extension.Cotangent.ext
    rfl
  map_smul' r x := by
    ext
    simp [Algebra.Extension.Cotangent.val_smul'']

@[simp] lemma quotientExtensionCotangentEquivKer_val (f : K[X])
    (x : (quotientExtension f).ker.Cotangent) :
    (quotientExtensionCotangentEquivKer f x).val = x.val := rfl
""",
        "Spt2 expose extension-cotangent transport value",
    )

    changed |= replace_once(
        spt2,
        """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]
  exact LinearEquiv.refl K _
""",
        """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]
  exact LinearEquiv.refl K _

@[simp] lemma quotientSpanCotangentEquivKer_val (f : K[X])
    (x : (Ideal.span ({f} : Set K[X])).Cotangent) :
    (quotientSpanCotangentEquivKer f x).val = x.val := by
  simp [quotientSpanCotangentEquivKer, quotientExtension_ker]
""",
        "Spt2 expose ideal-cotangent transport value",
    )

    changed |= replace_once(
        spt2,
        """  ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  unfold principalCotangentQuotEquiv quotientExtensionCotangentEquivKer
  rw [LinearEquiv.ofBijective_apply, hmap]
  simp [quotientSpanCotangentEquivKer, quotientExtension_ker,
    Algebra.Extension.Cotangent.val_mk, Algebra.Extension.Cotangent.val_of]
""",
        """  apply Algebra.Extension.Cotangent.ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_val,
    quotientSpanCotangentEquivKer_val]
  unfold principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply, hmap]
  rfl
""",
        "Spt2 prove conormal generator through value computation lemmas",
    )

    print("SPT closure repairs changed sources." if changed else "No SPT closure changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
