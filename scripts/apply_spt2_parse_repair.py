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


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    old_count = text.count(OLD)
    new_count = text.count(NEW)
    if old_count == 1:
        PATH.write_text(text.replace(OLD, NEW, 1), encoding="utf-8", newline="\n")
        print("Spt2: closed Algebra.Extension.Cotangent.of application")
        return 0
    if old_count == 0 and new_count == 1:
        print("Spt2: cotangent application repair already applied")
        return 0
    raise RuntimeError(
        f"Spt2 cotangent parse repair: expected one old or new match; old={old_count}, new={new_count}"
    )


if __name__ == "__main__":
    raise SystemExit(main())
