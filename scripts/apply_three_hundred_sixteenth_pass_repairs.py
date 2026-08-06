from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(
    text: str,
    old: str,
    new: str,
    label: str,
    expected: int = 1,
) -> str:
    actual = text.count(old)
    print(f"{label}: expected={expected} actual={actual}")
    if actual != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {actual}")
    return text.replace(old, new)


def main() -> int:
    text = M2A.read_text(encoding="utf-8")

    # The finite checklist evidence family left the universe of the
    # unnumbered-formula branch unconstrained.  Select the canonical level-0
    # instance of the already universe-polymorphic evidence theorem.  This
    # changes neither a mathematical statement nor any proof-producing API.
    text = replace_exact(
        text,
        "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence c\n",
        "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence.{0} c\n",
        "Mock2 Advanced specialize unnumbered checklist evidence universe",
    )
    text = replace_exact(
        text,
        "    · exact UnnumberedFormulaLedger.claimEvidence c\n",
        "    · exact UnnumberedFormulaLedger.claimEvidence.{0} c\n",
        "Mock2 Advanced specialize unnumbered checklist proof universe",
    )

    M2A.write_text(text, encoding="utf-8")
    print("[pass316] Mock2_Advanced checklist universe frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
