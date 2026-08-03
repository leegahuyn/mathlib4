from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Spt2.lean")

BAD_EXTENSION_VAL = """@[simp] lemma quotientExtensionCotangentEquivKer_val (f : K[X])
    (x : (quotientExtension f).ker.Cotangent) :
    (quotientExtensionCotangentEquivKer f x).val = x.val := rfl

"""

BAD_SPAN_VAL = """@[simp] lemma quotientSpanCotangentEquivKer_val (f : K[X])
    (x : (Ideal.span ({f} : Set K[X])).Cotangent) :
    (quotientSpanCotangentEquivKer f x).val = x.val := by
  simp [quotientSpanCotangentEquivKer, quotientExtension_ker]

"""

OLD_DEFINITION = """noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    ((quotientSpanCotangentEquivKer f).trans
      (quotientExtensionCotangentEquivKer f))
"""

NEW_DEFINITION = """noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    (((Ideal.cotangentEquivOfEq (quotientExtension_ker f).symm).restrictScalars K).trans
      (quotientExtensionCotangentEquivKer f))
"""

OLD_PROOFS = [
"""  apply Algebra.Extension.Cotangent.ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_val,
    quotientSpanCotangentEquivKer_val]
  unfold principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply, hmap]
  rfl
""",
"""  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  rw [quotientSpanCotangentEquivKer, quotientExtension_ker]
  unfold principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply, hmap]
  rfl
""",
"""  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  rw [hprincipal, hmap]
  change Algebra.Extension.Cotangent.of
      (quotientSpanCotangentEquivKer f
        ((Ideal.span ({f} : Set K[X])).toCotangent
          ⟨a * f, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩)) =
    Algebra.Extension.Cotangent.mk
      (P := quotientExtension f)
      ⟨a * f, by
        rw [quotientExtension_ker]
        exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩
  apply Algebra.Extension.Cotangent.ext
  simp [quotientSpanCotangentEquivKer, quotientExtension_ker,
    Algebra.Extension.Cotangent.val_mk, Algebra.Extension.Cotangent.val_of]
""",
]

NEW_PROOF = """  ext
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
"""


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False
    for bad, label in ((BAD_EXTENSION_VAL, "extension quotient projection"),
                       (BAD_SPAN_VAL, "span quotient projection")):
        count = text.count(bad)
        if count == 1:
            text = text.replace(bad, "")
            changed = True
            print(f"Spt2 remove invalid {label}: applied")
        elif count > 1:
            raise RuntimeError(f"Spt2 {label}: expected at most one match, found {count}")
    count = text.count(OLD_DEFINITION)
    if count == 1:
        text = text.replace(OLD_DEFINITION, NEW_DEFINITION)
        changed = True
        print("Spt2 direct cotangent equality transport: applied")
    elif count > 1:
        raise RuntimeError(f"Spt2 definition: expected at most one match, found {count}")
    proof_changed = False
    for old in OLD_PROOFS:
        count = text.count(old)
        if count == 1:
            text = text.replace(old, NEW_PROOF)
            changed = True
            proof_changed = True
            print("Spt2 cotangent generator proof: applied")
            break
        if count > 1:
            raise RuntimeError(f"Spt2 proof: expected at most one match, found {count}")
    if not proof_changed:
        print("Spt2 cotangent generator proof: already applied/source changed")
    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
