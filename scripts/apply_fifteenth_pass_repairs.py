from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Spt2.lean")

OLD_EQUIV = """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]
  exact LinearEquiv.refl K _
"""

NEW_EQUIV = """noncomputable def idealCotangentEquivOfEqKX
    (I J : Ideal K[X]) (h : I = J) : I.Cotangent ≃ₗ[K] J.Cotangent := by
  subst J
  exact LinearEquiv.refl K _

@[simp] lemma idealCotangentEquivOfEqKX_toCotangent
    (I J : Ideal K[X]) (h : I = J) (x : I) :
    idealCotangentEquivOfEqKX I J h (I.toCotangent x) =
      J.toCotangent (LinearEquiv.ofEq I J h x) := by
  subst J
  rfl

noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent :=
  idealCotangentEquivOfEqKX
    (Ideal.span ({f} : Set K[X])) (quotientExtension f).ker
    (quotientExtension_ker f).symm

@[simp] lemma quotientSpanCotangentEquivKer_toCotangent
    (f : K[X]) (x : Ideal.span ({f} : Set K[X])) :
    quotientSpanCotangentEquivKer f
        ((Ideal.span ({f} : Set K[X])).toCotangent x) =
      (quotientExtension f).ker.toCotangent
        ⟨x.1, (quotientExtension_ker f).symm ▸ x.2⟩ := by
  let J : Ideal K[X] := (quotientExtension f).ker
  let h : Ideal.span ({f} : Set K[X]) = J := (quotientExtension_ker f).symm
  change idealCotangentEquivOfEqKX (Ideal.span ({f} : Set K[X])) J h
      ((Ideal.span ({f} : Set K[X])).toCotangent x) =
    J.toCotangent ⟨x.1, h ▸ x.2⟩
  rw [idealCotangentEquivOfEqKX_toCotangent]
  congr 1
"""

OLD_PROOF = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  cases quotientExtension_ker f
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

PREVIOUS_PROOF = OLD_PROOF.replace("  cases quotientExtension_ker f\n", "")

NEW_PROOF = """  have hprincipal :
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
      ⟨a * f, (quotientExtension_ker f).symm ▸
        Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩
  rw [hprincipal, hmap]
  apply Algebra.Extension.Cotangent.ext
  simp only [Algebra.Extension.Cotangent.val_of,
    Algebra.Extension.Cotangent.val_mk]
  rw [quotientSpanCotangentEquivKer_toCotangent]
"""


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        raise RuntimeError(f"{label}: source anchor not found")
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    text, did = replace_once(
        text, OLD_EQUIV, NEW_EQUIV,
        "Spt2 ideal-typed cotangent equality equivalence")
    changed |= did

    if NEW_PROOF not in text:
        if OLD_PROOF in text:
            text = text.replace(OLD_PROOF, NEW_PROOF, 1)
            print("Spt2 generator transport via specialized cotangent lemma: applied")
            changed = True
        elif PREVIOUS_PROOF in text:
            text = text.replace(PREVIOUS_PROOF, NEW_PROOF, 1)
            print("Spt2 generator transport via specialized cotangent lemma: applied")
            changed = True
        else:
            raise RuntimeError("Spt2 generator proof anchor not found")
    else:
        print("Spt2 generator transport via specialized cotangent lemma: already applied")

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
