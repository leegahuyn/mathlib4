from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """  compatible := IsManifold.compatible
""",
        """  compatible := by
    apply StructureGroupoid.compatible
""",
        "Mock2 inherit manifold compatibility through the actual structure groupoid",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  field_simp [hτ]
  ring_nf

theorem factor_sq""",
        """  field_simp [hτ]
  simpa [mul_comm]

theorem factor_sq""",
        "Mock2 Advanced close the base product by commutativity after denominator clearing",
    )
    m2a = replace_exact(
        m2a,
        """  norm_num [Matrix.mul_fin_two] <;> ring_nf
""",
        """  norm_num [pow_two, Matrix.mul_fin_two] <;> ring_nf
""",
        "Mock2 Advanced unfold the matrix square before evaluating the denominator",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
