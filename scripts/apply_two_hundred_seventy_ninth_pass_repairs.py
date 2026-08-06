from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


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
        "FiniteCoverSheafData I",
        "FiniteCoverSheafData.{u, v} I",
        "Mock2 fix the finite-cover data universes explicitly",
        expected=7,
    )
    M2.write_text(m2, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem graphExtension_range_isClosed :
    IsClosed (Set.range Q.graphExtension) := by
  simpa only [graphExtensionIsometry] using
    Q.graphExtensionIsometry.isometry.isClosedEmbedding.isClosed_range
""",
        """theorem graphExtension_range_isClosed :
    IsClosed (Set.range Q.graphExtension) := by
  simpa [graphExtensionIsometry] using
    Q.graphExtensionIsometry.isometry.isClosedEmbedding.isClosed_range
""",
        "FunctionalAnalysis normalize the WithLp topology in the closed-range theorem",
    )
    fa = replace_exact(
        fa,
        "Set.closure",
        "closure",
        "FunctionalAnalysis use the current unqualified closure notation",
        expected=3,
    )
    fa = replace_exact(
        fa,
        "WithLp.norm_fst_le (Q.graphExtension x).snd",
        "WithLp.norm_fst_le HR (Q.graphExtension x).snd",
        "FunctionalAnalysis supply the inner first-coordinate type",
    )
    fa = replace_exact(
        fa,
        "WithLp.norm_fst_le (Q.graphExtension x)",
        "WithLp.norm_fst_le H₀ (Q.graphExtension x)",
        "FunctionalAnalysis supply the outer first-coordinate type",
    )
    fa = replace_exact(
        fa,
        "WithLp.norm_snd_le (Q.graphExtension x).snd",
        "WithLp.norm_snd_le HR (Q.graphExtension x).snd",
        "FunctionalAnalysis supply the inner second-coordinate type",
    )
    fa = replace_exact(
        fa,
        "WithLp.norm_snd_le (Q.graphExtension x)",
        "WithLp.norm_snd_le H₀ (Q.graphExtension x)",
        "FunctionalAnalysis supply the outer second-coordinate type",
        expected=2,
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
