from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    old_count = text.count(old)
    new_count = text.count(new)
    print(f"{label}: expected=1 old={old_count} new={new_count}")
    if old_count == 1 and new_count == 0:
        print(f"{label}: before={old.splitlines()[0]!r}")
        print(f"{label}: after={new.splitlines()[0]!r}")
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
    text = replace_once(
        text,
        "      KernelEvidence (@UnnumberedFormulaLedger.section7C_quantitativeTailBound_proved)\n",
        "      KernelEvidence (@UnnumberedFormulaLedger.section7C_quantitativeTailBound_proved.{0})\n",
        "Mock2 Advanced Section7 quantitative-tail evidence universe",
    )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass313] Mock2_Advanced Section7 evidence universe repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
