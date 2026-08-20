from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
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
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.toInnerProductSpaceReal

/-- Exact tangent formula for the cusp at zero. -/
""",
        """attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] Complex.addCommGroup

/-- Exact tangent formula for the cusp at zero. -/
""",
        "Mock2 Advanced align the reciprocal derivative additive structure",
    )
    m2a = replace_exact(
        m2a,
        """attribute [instance] RCLike.toInnerProductSpaceReal
attribute [instance 2000] NormedSpace.complexToReal

/-! ##### Finite assembly of the complete truncated boundary -/
""",
        """attribute [instance] Complex.addCommGroup
attribute [instance] RCLike.toInnerProductSpaceReal
attribute [instance 2000] NormedSpace.complexToReal

/-! ##### Finite assembly of the complete truncated boundary -/
""",
        "Mock2 Advanced restore the canonical complex additive structure",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    start = "namespace WeightCorePetersson\n"
    end = "end WeightCorePetersson\n"
    replacements = [
        ("u.toSection", "SmoothCompactWeightCore.toSection u", 29,
         "FunctionalAnalysis qualify u compact-core sections"),
        ("v.toSection", "SmoothCompactWeightCore.toSection v", 14,
         "FunctionalAnalysis qualify v compact-core sections"),
        ("w.toSection", "SmoothCompactWeightCore.toSection w", 4,
         "FunctionalAnalysis qualify w compact-core sections"),
        ("u.continuous", "SmoothCompactWeightCore.continuous u", 2,
         "FunctionalAnalysis qualify u continuity proofs"),
        ("v.continuous", "SmoothCompactWeightCore.continuous v", 1,
         "FunctionalAnalysis qualify v continuity proofs"),
        ("u.quotientCompact", "SmoothCompactWeightCore.quotientCompact u", 2,
         "FunctionalAnalysis qualify u quotient compactness"),
        ("v.quotientCompact", "SmoothCompactWeightCore.quotientCompact v", 1,
         "FunctionalAnalysis qualify v quotient compactness"),
    ]
    for old, new, expected, label in replacements:
        fa = replace_in_block(fa, start, end, old, new, expected, label)
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
