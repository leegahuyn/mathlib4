from __future__ import annotations

from pathlib import Path
import re

import apply_seventy_eighth_pass_repairs as pass78
import apply_seventy_ninth_pass_repairs as pass79
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("namespace GenuineWeightedSobolev")
    end = text.index("end GenuineWeightedSobolev", start)
    block = text[start:end]
    replacements = {
        "IsAutomorphic ν":
            "GenuineInverseHalfWeightAutomorphy.IsAutomorphic ν",
        "IsAEAutomorphic ν":
            "GenuineInverseHalfWeightAutomorphy.IsAEAutomorphic ν",
    }
    for old, new in replacements.items():
        block, count = re.subn(
            rf"(?<![A-Za-z0-9_.]){re.escape(old)}", new, block)
        if count:
            changed = True
            print(f"Mock2Advanced qualify {old}: applied {count}")
    text = text[:start] + block + text[end:]

    text, did = replace_exact(
        text,
        """  apply hclosure
  simpa only [Submodule.topologicalClosure_coe] using u.property
""",
        """  apply hclosure
  rw [← Submodule.topologicalClosure_coe]
  exact u.property
""",
        1,
        "Mock2Advanced transport Sobolev membership across topological closure",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """      simp_rw [abelRemainder]
      ring
""",
        """      simp only [abelRemainder] at ih ⊢
      ring
""",
        1,
        "Mock2Advanced unfold finite Abel remainders in the hypothesis and goal",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass78.main()
    pass79.repair_mock1_advanced()
    pass79.repair_mock2()
    repair_mock2_advanced()
    pass79.repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
