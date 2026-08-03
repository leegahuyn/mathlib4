from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Spt2.lean")

DIRECT_DEFINITION = """noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    (((Ideal.cotangentEquivOfEq (quotientExtension_ker f).symm).restrictScalars K).trans
      (quotientExtensionCotangentEquivKer f))
"""

CANONICAL_DEFINITION = """noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    ((quotientSpanCotangentEquivKer f).trans
      (quotientExtensionCotangentEquivKer f))
"""

DIRECT_PROOF = """  ext
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

REWRITE_PROOF = """  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  rw [quotientSpanCotangentEquivKer, quotientExtension_ker]
  unfold principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply, hmap]
  rfl
"""

CANONICAL_PROOF = """  have hker : (quotientExtension f).ker = Ideal.span ({f} : Set K[X]) :=
    quotientExtension_ker f
  cases hker
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, quotientExtensionCotangentEquivKer_apply]
  unfold quotientSpanCotangentEquivKer principalCotangentQuotEquiv
  rw [LinearEquiv.ofBijective_apply, hmap]
  rfl
"""


def replace_at_most_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False
    text, did = replace_at_most_once(
        text, DIRECT_DEFINITION, CANONICAL_DEFINITION,
        "Spt2 canonical conormal definition")
    changed |= did
    for old in (DIRECT_PROOF, REWRITE_PROOF):
        text, did = replace_at_most_once(
            text, old, CANONICAL_PROOF,
            "Spt2 canonical conormal generator proof")
        changed |= did
        if did:
            break
    if not changed:
        print("Spt2 canonical final: already applied/source changed")
    else:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
