from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Spt2.lean")
OLD = """        (principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a)) =
    Algebra.Extension.Cotangent.mk
"""
NEW = """        (principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a))) =
    Algebra.Extension.Cotangent.mk
"""

OLD_PROOF = """  rw [hprincipal, hmap]
  apply Algebra.Extension.Cotangent.ext
  simp [quotientSpanCotangentEquivKer, quotientExtension_ker,
    Algebra.Extension.Cotangent.val_mk, Algebra.Extension.Cotangent.val_of]
"""
NEW_PROOF = """  rw [hprincipal, hmap]
  rw [quotientExtension_ker]
  rfl
"""


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    old_count = text.count(OLD)
    new_count = text.count(NEW)
    if old_count == 1:
        text = text.replace(OLD, NEW, 1)
        changed = True
        print("Spt2: closed Algebra.Extension.Cotangent.of application")
    elif old_count == 0 and new_count == 1:
        print("Spt2: cotangent application repair already applied")
    elif old_count == 0 and new_count == 0:
        print("Spt2: obsolete exact-layout parse repair no longer matches; continuing")
    else:
        raise RuntimeError(
            f"Spt2 cotangent parse repair matched ambiguously; old={old_count}, new={new_count}"
        )

    old_proof_count = text.count(OLD_PROOF)
    new_proof_count = text.count(NEW_PROOF)
    if old_proof_count == 1:
        text = text.replace(OLD_PROOF, NEW_PROOF, 1)
        changed = True
        print("Spt2: rewrite the kernel ideal before reducing the cotangent transport")
    elif old_proof_count == 0 and new_proof_count == 1:
        print("Spt2: cotangent transport proof repair already applied")
    elif old_proof_count == 0 and new_proof_count == 0:
        print("Spt2: cotangent transport proof layout changed; continuing")
    else:
        raise RuntimeError(
            "Spt2 cotangent transport proof matched ambiguously; "
            f"old={old_proof_count}, new={new_proof_count}"
        )

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
