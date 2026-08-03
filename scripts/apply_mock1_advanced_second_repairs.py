from __future__ import annotations

import re
from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    old = """  unfold PairCompatible
  rw [h]
  simp
"""
    new = """  unfold PairCompatible
  rw [h]
  omega
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True

    text2, n = re.subn(r"(?m)^def EntropyModel\b", "noncomputable def EntropyModel", text, count=1)
    if n:
        text = text2; changed = True

    old = """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  cases key <;> decide
"""
    new = """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  classical
  cases key <;> simp [all]
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True

    text = text.replace(
        "simpa [referenceQSeries] using referenceEntropyAsymptotic",
        "simpa [referenceQSeries, referenceObjectQSeries] using referenceEntropyAsymptotic")
    text = text.replace(
        "simpa [referenceQSeries] using referenceRademacherExpansion",
        "simpa [referenceQSeries, referenceObjectQSeries] using referenceRademacherExpansion")

    text2, n = re.subn(
        r"(theorem coverage_targets_[A-Za-z0-9_']+\s*:[\s\S]*?\s*:= by)\n  decide",
        r"\1\n  classical\n  simp [targets]",
        text,
    )
    if n:
        text = text2; changed = True

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
