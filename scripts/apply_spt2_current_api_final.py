from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Spt2.lean")

CURRENT_BLOCK = """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]
  exact LinearEquiv.refl K _

@[simp] lemma quotientSpanCotangentEquivKer_toCotangent (f : K[X])
    (x : Ideal.span ({f} : Set K[X])) :
    quotientSpanCotangentEquivKer f
        ((Ideal.span ({f} : Set K[X])).toCotangent x) =
      (quotientExtension f).ker.toCotangent
        (LinearEquiv.ofEq _ _ (quotientExtension_ker f).symm x) := by
  rw [quotientExtension_ker]
  rfl

noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    ((quotientSpanCotangentEquivKer f).trans
      (quotientExtensionCotangentEquivKer f))
"""

DIRECT_BLOCK = """noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    (((Ideal.Cotangent.equivOfEq
        (Ideal.span ({f} : Set K[X])) (quotientExtension f).ker
        (quotientExtension_ker f).symm).restrictScalars K).trans
      (quotientExtensionCotangentEquivKer f))
"""

CURRENT_PROOF = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  apply Algebra.Extension.Cotangent.ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  rw [hprincipal, hmap, quotientSpanCotangentEquivKer_toCotangent]
  congr 1
"""

DIRECT_PROOF = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  change Algebra.Extension.Cotangent.of
      ((Ideal.Cotangent.equivOfEq
        (Ideal.span ({f} : Set K[X])) (quotientExtension f).ker
        (quotientExtension_ker f).symm)
        (principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a))) =
    Algebra.Extension.Cotangent.mk
      (P := quotientExtension f)
      ⟨a * f, by
        rw [quotientExtension_ker]
        exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩
  rw [hprincipal, hmap, Ideal.Cotangent.equivOfEq_toCotangent]
  rfl
"""

PATCHED_PROOF = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  apply Algebra.Extension.Cotangent.ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  rw [hprincipal, hmap, quotientSpanCotangentEquivKer_toCotangent]
  congr 1
  rw [quotientExtension_ker]
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
    text, did = replace_once(text, CURRENT_BLOCK, DIRECT_BLOCK,
        "Spt2 direct current Ideal.Cotangent transport")
    changed |= did
    text, did = replace_once(text, CURRENT_PROOF, PATCHED_PROOF,
        "Spt2 reduce dependent cotangent cast after congruence")
    changed |= did
    text, did = replace_once(text, DIRECT_PROOF, PATCHED_PROOF,
        "Spt2 replace direct conormal generator proof")
    changed |= did
    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
