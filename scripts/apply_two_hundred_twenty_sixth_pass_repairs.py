from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro τ hτ
  change cuspHeight κ τ = Y at hτ
  exact (not_lt_of_ge hY) (hτ ▸ cuspHeight_pos κ τ)
""",
        """  ext τ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hτ
  change cuspHeight κ τ = Y at hτ
  exact (not_lt_of_ge hY) (hτ ▸ cuspHeight_pos κ τ)
""",
        "Mock2_Advanced prove the empty cusp level by extensionality",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
