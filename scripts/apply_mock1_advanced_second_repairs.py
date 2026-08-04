from __future__ import annotations

import re
from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")


def replace_once_if_present(text: str, old: str, new: str) -> tuple[str, bool]:
    if old in text:
        return text.replace(old, new, 1), True
    return text, False


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
    text, did_change = replace_once_if_present(text, old, new)
    changed |= did_change

    text2, n = re.subn(r"(?m)^def EntropyModel\b", "noncomputable def EntropyModel", text, count=1)
    if n:
        text = text2
        changed = True

    old = """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  cases key <;> decide
"""
    new = """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  classical
  cases key <;> simp [all]
"""
    text, did_change = replace_once_if_present(text, old, new)
    changed |= did_change

    replacements = [
        (
            "simpa [referenceQSeries] using referenceEntropyAsymptotic",
            "simpa [referenceQSeries, referenceObjectQSeries] using referenceEntropyAsymptotic",
        ),
        (
            "simpa [referenceQSeries] using referenceRademacherExpansion",
            "simpa [referenceQSeries, referenceObjectQSeries] using referenceRademacherExpansion",
        ),
    ]
    for old, new in replacements:
        if old in text:
            text = text.replace(old, new)
            changed = True

    text2, n = re.subn(
        r"(theorem coverage_targets_[A-Za-z0-9_']+\s*:[\s\S]*?\s*:= by)\n  decide",
        r"\1\n  classical\n  simp [targets]",
        text,
    )
    if n:
        text = text2
        changed = True

    section_lists = [
        "objectSchemaRequirements",
        "t1t5Requirements",
        "sptRequirements",
        "kernelRequirements",
        "exactCoefficientRequirements",
        "pAdicRequirements",
        "entropyReproRequirements",
        "finalInstanceRequirements",
    ]
    for name in section_lists:
        old = f"  cases r <;>\n    simp [{name}, sectionOf] at h ⊢"
        new = f"  cases r <;>\n    simp_all [{name}, sectionOf]"
        if old in text:
            text = text.replace(old, new, 1)
            changed = True
        elif new in text:
            print(f"{name}: already repaired")
        else:
            # The source has moved beyond this exact deterministic form. Do not
            # abort unrelated matrix jobs before Lean can report the real error.
            print(f"{name}: exact section proof pattern absent; leaving source unchanged")

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("Mock1_Advanced second-pass repairs changed source.")
    else:
        print("Mock1_Advanced second-pass repairs made no changes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
