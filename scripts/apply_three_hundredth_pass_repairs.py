from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    text = M2A.read_text(encoding="utf-8")
    text = replace_exact(
        text,
        """  exact hcomplex.comp_ofReal
""",
        """  simpa [mul_comm] using hcomplex.comp_ofReal
""",
        "Mock2 Advanced unitary derivative multiplication order",
    )
    text = replace_exact(
        text,
        """set_option maxHeartbeats 1000000 maxRecDepth 10000 in
instance : Fintype Requirement where
""",
        """set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
instance : Fintype Requirement where
""",
        "Mock2 Advanced nested Requirement resource options",
        expected=2,
    )
    text = replace_exact(
        text,
        """theorem requirement_count : Fintype.card Requirement = 50 := by
  decide
""",
        """set_option maxRecDepth 10000 in
theorem requirement_count : Fintype.card Requirement = 50 := by
  decide
""",
        "Mock2 Advanced requirement counts",
        expected=2,
    )
    text = replace_exact(
        text,
        """  | definition4 => exact fun h =>
      simp only [ClaimEvidence]
      h.exists_eventual_positive
""",
        """  | definition4 =>
      simp only [ClaimEvidence]
      exact fun h => h.exists_eventual_positive
""",
        "Mock2 Advanced Section 5.1 definition4 evidence",
    )
    text = replace_exact(
        text,
        """  | definition7 => exact fun h hm =>
      simp only [ClaimEvidence]
      h.mass_pos hm
""",
        """  | definition7 =>
      simp only [ClaimEvidence]
      exact fun h hm => h.mass_pos hm
""",
        "Mock2 Advanced Section 5.1 definition7 evidence",
    )
    text = replace_exact(
        text,
        """  | definition13 => exact fun C =>
      simp only [ClaimEvidence]
      C.pure_tensor_rule
""",
        """  | definition13 =>
      simp only [ClaimEvidence]
      exact fun C => C.pure_tensor_rule
""",
        "Mock2 Advanced Section 5.1 definition13 evidence",
    )
    text = replace_exact(
        text,
        """theorem item_count : Fintype.card Item = 174 := by
  decide
""",
        """set_option maxRecDepth 10000 in
theorem item_count : Fintype.card Item = 174 := by
  decide
""",
        "Mock2 Advanced combined checklist count",
    )
    M2A.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
