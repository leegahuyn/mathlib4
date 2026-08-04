from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Spt2.lean")


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    old = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
"""
    new = """  have hprincipal :
      principalCotangentQuotEquiv (R := K[X]) (poly := f) hf
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) =
        principalCotangentQuotMap f
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a) := rfl
  cases quotientExtension_ker f
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
"""
    if new in text:
        print("Spt2 dependent kernel transport: already normalized")
        return 0
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one Spt2 kernel-transport anchor, found {count}")
    PATH.write_text(text.replace(old, new, 1), encoding="utf-8", newline="\n")
    print("Spt2 dependent kernel transport: eliminated by equality induction")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
