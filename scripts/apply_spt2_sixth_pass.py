from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Spt2.lean")

OLD_LEMMA = """@[simp] lemma quotientSpanCotangentEquivKer_toCotangent (f : K[X])
    (x : Ideal.span ({f} : Set K[X])) :
    quotientSpanCotangentEquivKer f
        ((Ideal.span ({f} : Set K[X])).toCotangent x) =
      (quotientExtension f).ker.toCotangent
        (LinearEquiv.ofEq _ _ (quotientExtension_ker f).symm x) :=
  Ideal.Cotangent.equivOfEq_toCotangent _ _ _ x
"""

NEW_LEMMA = """@[simp] lemma quotientSpanCotangentEquivKer_toCotangent (f : K[X])
    (x : Ideal.span ({f} : Set K[X])) :
    quotientSpanCotangentEquivKer f
        ((Ideal.span ({f} : Set K[X])).toCotangent x) =
      (quotientExtension f).ker.toCotangent
        (LinearEquiv.ofEq _ _ (quotientExtension_ker f).symm x) := by
  change (Ideal.Cotangent.equivOfEq
      (Ideal.span ({f} : Set K[X])) (quotientExtension f).ker
      (quotientExtension_ker f).symm)
        ((Ideal.span ({f} : Set K[X])).toCotangent x) = _
  exact Ideal.Cotangent.equivOfEq_toCotangent
    (Ideal.span ({f} : Set K[X])) (quotientExtension f).ker
    (quotientExtension_ker f).symm x
"""

OLD_PROOF = """  apply Algebra.Extension.Cotangent.ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  unfold principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply, hmap,
    quotientSpanCotangentEquivKer_toCotangent]
  congr 1
  apply Subtype.ext
  rfl
"""

NEW_PROOF = """  apply Algebra.Extension.Cotangent.ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          (Submodule.Quotient.mk a :
            K[X] ⧸ (Ideal.span ({f} : Set K[X]) : Ideal K[X])) =
        principalCotangentQuotMap f
          (Submodule.Quotient.mk a :
            K[X] ⧸ (Ideal.span ({f} : Set K[X]) : Ideal K[X])) := rfl
  rw [hprincipal, hmap, quotientSpanCotangentEquivKer_toCotangent]
  congr 1
  apply Subtype.ext
  rfl
"""


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False
    if OLD_LEMMA in text:
        text = text.replace(OLD_LEMMA, NEW_LEMMA, 1)
        changed = True
    if OLD_PROOF in text:
        text = text.replace(OLD_PROOF, NEW_PROOF, 1)
        changed = True
    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
