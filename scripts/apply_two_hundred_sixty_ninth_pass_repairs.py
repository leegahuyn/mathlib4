from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  map_add' u v := by
    simpa only [map_add, WithLp.toLp_add]
  map_smul' c u := by
    simpa only [map_smul, RingHom.id_apply, WithLp.toLp_smul]
""",
        """  map_add' u v := by
    simp only [map_add]
    change WithLp.toLp 2
      ((Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u)) +
        (Q.base v, WithLp.toLp 2 (Q.raised v, Q.lowered v))) =
      WithLp.toLp 2 (Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u)) +
        WithLp.toLp 2 (Q.base v, WithLp.toLp 2 (Q.raised v, Q.lowered v))
    exact WithLp.toLp_add 2 _ _
  map_smul' c u := by
    simp only [map_smul, RingHom.id_apply]
    change WithLp.toLp 2
      (c • (Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u))) =
      c • WithLp.toLp 2 (Q.base u, WithLp.toLp 2 (Q.raised u, Q.lowered u))
    exact WithLp.toLp_smul 2 c _
""",
        "FunctionalAnalysis supply the explicit L2 index to graph linearity",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
