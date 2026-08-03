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

@[simp] lemma quotientExtensionCotangentEquivKer_apply (f : K[X])
    (x : (quotientExtension f).ker.Cotangent) :
    quotientExtensionCotangentEquivKer f x = Algebra.Extension.Cotangent.of x := rfl
""",
        "Spt2 expose extension-cotangent transport application",
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
        """  have hker : (quotientExtension f).ker = Ideal.span ({f} : Set K[X]) :=
    quotientExtension_ker f
  cases hker
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  unfold quotientSpanCotangentEquivKer principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply, hmap]
  rfl
""",
        "Spt2 eliminate the dependent ideal transport before computation",
    )

    print("SPT closure repairs changed sources." if changed else "No SPT closure changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
