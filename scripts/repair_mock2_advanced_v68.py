from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def rewrite_once(text: str, old: str, new: str, label: str) -> str:
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

    # The remaining Section7 ledger metavariable is the carrier universe of the
    # quantitative finite-series tail theorem.  The evidence row is closed data,
    # so select the existing theorem at Type 0 without changing its statement.
    text = rewrite_once(
        text,
        "        (@UnnumberedFormulaLedger.section7C_quantitativeTailBound_proved)\n",
        "        (@UnnumberedFormulaLedger.section7C_quantitativeTailBound_proved.{0})\n",
        "v68 finite-series tail evidence universe",
    )

    # The remaining P0 ledger metavariables are the four form-carrier universes
    # of CurvatureMorphism.map_curvature.  Again this only instantiates an
    # already-proved polymorphic theorem for a closed audit row.
    text = rewrite_once(
        text,
        "      KernelEvidence (@p07_typedCurvature_correctedAndProved)\n",
        "      KernelEvidence (@p07_typedCurvature_correctedAndProved.{0, 0, 0, 0})\n",
        "v68 curvature evidence universes",
    )

    # UnnumberedFormulaLedger.ClaimEvidence and claimEvidence are not universe
    # polymorphic.  Earlier v68 text incorrectly supplied .{0}, which Lean
    # reports as too many explicit universe levels; restore the actual API.
    text = rewrite_once(
        text,
        "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence.{0} c\n",
        "  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence c\n",
        "v68 unnumbered checklist evidence API",
    )
    text = rewrite_once(
        text,
        "    · exact UnnumberedFormulaLedger.claimEvidence.{0} c\n",
        "    · exact UnnumberedFormulaLedger.claimEvidence c\n",
        "v68 unnumbered checklist proof API",
    )

    TARGET.write_text(text, encoding="utf-8")
    print("[v68] Mock2_Advanced final evidence universes repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
