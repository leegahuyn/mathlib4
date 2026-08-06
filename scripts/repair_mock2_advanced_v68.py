from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def specialize_once(text: str, old: str, new: str, label: str) -> str:
    old_count = text.count(old)
    new_count = text.count(new)
    print(f"{label}: old={old_count} new={new_count}")
    if old_count == 1 and new_count == 0:
        return text.replace(old, new)
    if old_count == 0 and new_count == 1:
        print(f"{label}: already applied")
        return text
    raise RuntimeError(
        f"{label}: expected exactly one unrepaired or repaired occurrence, "
        f"found old={old_count}, new={new_count}"
    )


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")

    # v68 resolves the final unconstrained universe metavariable in the
    # unnumbered-formula evidence branch by selecting level 0 of the existing
    # universe-polymorphic evidence declarations.  It changes no theorem
    # statement, assumption, certificate field, or proof boundary.
    text = specialize_once(
        text,
        "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence c\n",
        "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence.{0} c\n",
        "v68 checklist evidence universe",
    )
    text = specialize_once(
        text,
        "    · exact UnnumberedFormulaLedger.claimEvidence c\n",
        "    · exact UnnumberedFormulaLedger.claimEvidence.{0} c\n",
        "v68 checklist proof universe",
    )

    TARGET.write_text(text, encoding="utf-8")
    print("[v68] Mock2_Advanced unnumbered-formula evidence universe repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
