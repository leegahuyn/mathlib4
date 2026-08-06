from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def replace_in_block(
    text: str,
    start_marker: str,
    end_marker: str,
    old: str,
    new: str,
    expected: int,
    label: str,
) -> str:
    start = text.index(start_marker)
    end = text.index(end_marker, start)
    block = text[start:end]
    count = block.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    block = block.replace(old, new)
    print(f"{label}: applied {count}")
    return text[:start] + block + text[end:]


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """  add_zero A := by apply ext_pointwise; intro τ; simp [add, zero]
  zero_add A := by apply ext_pointwise; intro τ; simp [add, zero]
  add_comm A C := by apply ext_pointwise; intro τ; exact add_comm _ _
  add_assoc A C D := by apply ext_pointwise; intro τ; exact add_assoc _ _ _
  neg_add_cancel A := by apply ext_pointwise; intro τ; simp [add, neg, zero]
""",
        """  add_zero A := by
    apply ext_pointwise
    intro τ
    exact add_zero (A τ)
  zero_add A := by
    apply ext_pointwise
    intro τ
    exact zero_add (A τ)
  add_comm A C := by apply ext_pointwise; intro τ; exact add_comm _ _
  add_assoc A C D := by apply ext_pointwise; intro τ; exact add_assoc _ _ _
  neg_add_cancel A := by
    apply ext_pointwise
    intro τ
    exact neg_add_cancel (A τ)
""",
        "Mock2 prove smooth one-form additive laws pointwise",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] Complex.addCommGroup

/-- Exact tangent formula for the cusp at zero. -/
""",
        """attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] Complex.addCommGroup
attribute [-instance] Complex.instRing

/-- Exact tangent formula for the cusp at zero. -/
""",
        "Mock2 Advanced align the reciprocal derivative ring structure",
    )
    m2a = replace_exact(
        m2a,
        """attribute [instance] Complex.addCommGroup
attribute [instance] RCLike.toInnerProductSpaceReal
attribute [instance 2000] NormedSpace.complexToReal
""",
        """attribute [instance] Complex.instRing
attribute [instance] Complex.addCommGroup
attribute [instance] RCLike.toInnerProductSpaceReal
attribute [instance 2000] NormedSpace.complexToReal
""",
        "Mock2 Advanced restore the canonical complex ring structure",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    start = "namespace WeightCorePetersson\n"
    end = "end WeightCorePetersson\n"
    replacements = [
        ("SmoothCompactWeightCore.toSection u", "(SmoothCompactWeightCore.toSection u)", 29,
         "FunctionalAnalysis parenthesize u compact-core sections"),
        ("SmoothCompactWeightCore.toSection v", "(SmoothCompactWeightCore.toSection v)", 14,
         "FunctionalAnalysis parenthesize v compact-core sections"),
        ("SmoothCompactWeightCore.toSection w", "(SmoothCompactWeightCore.toSection w)", 4,
         "FunctionalAnalysis parenthesize w compact-core sections"),
        ("SmoothCompactWeightCore.continuous u", "(SmoothCompactWeightCore.continuous u)", 2,
         "FunctionalAnalysis parenthesize u continuity proofs"),
        ("SmoothCompactWeightCore.continuous v", "(SmoothCompactWeightCore.continuous v)", 1,
         "FunctionalAnalysis parenthesize v continuity proofs"),
        ("SmoothCompactWeightCore.quotientCompact u", "(SmoothCompactWeightCore.quotientCompact u)", 2,
         "FunctionalAnalysis parenthesize u quotient compactness"),
        ("SmoothCompactWeightCore.quotientCompact v", "(SmoothCompactWeightCore.quotientCompact v)", 1,
         "FunctionalAnalysis parenthesize v quotient compactness"),
    ]
    for old, new, expected, label in replacements:
        fa = replace_in_block(fa, start, end, old, new, expected, label)
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
