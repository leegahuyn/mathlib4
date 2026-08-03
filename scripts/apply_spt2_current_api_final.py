from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Spt2.lean")

OLD_SPAN = """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]
  exact LinearEquiv.refl K _
"""

NEW_SPAN = """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent :=
  (Ideal.Cotangent.equivOfEq
    (Ideal.span ({f} : Set K[X])) (quotientExtension f).ker
    (quotientExtension_ker f).symm).restrictScalars K

@[simp] lemma quotientSpanCotangentEquivKer_toCotangent (f : K[X])
    (x : Ideal.span ({f} : Set K[X])) :
    quotientSpanCotangentEquivKer f
        ((Ideal.span ({f} : Set K[X])).toCotangent x) =
      (quotientExtension f).ker.toCotangent
        (LinearEquiv.ofEq _ _ (quotientExtension_ker f).symm x) := by
  simpa only [quotientSpanCotangentEquivKer,
    LinearEquiv.restrictScalars_apply] using
    (Ideal.Cotangent.equivOfEq_toCotangent
      (Ideal.span ({f} : Set K[X])) (quotientExtension f).ker
      (quotientExtension_ker f).symm x)
"""

OLD_PROOF = """  have hker : (quotientExtension f).ker = Ideal.span ({f} : Set K[X]) :=
    quotientExtension_ker f
  cases hker
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  unfold quotientSpanCotangentEquivKer principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply, hmap]
  rfl
"""

NEW_PROOF = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  apply Algebra.Extension.Cotangent.ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  rw [hprincipal, hmap, quotientSpanCotangentEquivKer_toCotangent]
  congr 1
  apply Subtype.ext
  rfl
"""


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied/source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False
    text, did = replace_once(text, OLD_SPAN, NEW_SPAN,
        "Spt2 current Ideal.Cotangent transport")
    changed |= did
    text, did = replace_once(text, OLD_PROOF, NEW_PROOF,
        "Spt2 current conormal generator proof")
    changed |= did
    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
