from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Spt2.lean")


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    old = """⟨a * f, by
          rw [quotientExtension_ker]
          exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩"""
    new = """⟨a * f, (quotientExtension_ker f).symm ▸
          Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩"""
    count = text.count(old)
    if count == 0:
        print("Spt2 explicit quotient-kernel membership transport: already applied/source changed")
        return 0
    text = text.replace(old, new)
    PATH.write_text(text, encoding="utf-8", newline="\n")
    print(f"Spt2 explicit quotient-kernel membership transport: applied {count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
