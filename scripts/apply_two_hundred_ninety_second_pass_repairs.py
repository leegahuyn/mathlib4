from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """namespace CorrectedLemmas.ScatteringDensityErratum

noncomputable def scalarUnitaryScattering (t : ℝ) : ℂ :=
""",
        """namespace CorrectedLemmas.ScatteringDensityErratum

/-- Use the canonical restriction-of-scalars normed-space structure consistently
throughout the real-parameter derivative calculation. -/
local instance scalarUnitaryRealNormedSpace : NormedSpace ℝ ℂ :=
  NormedSpace.complexToReal

noncomputable def scalarUnitaryScattering (t : ℝ) : ℂ :=
""",
        "Mock2 Advanced coherent real scalar structure",
    )
    m2a = replace_exact(
        m2a,
        """theorem correction_hasDerivAt (q : ℂ) :
    HasDerivAt correctionValue 1 q := by
  convert (hasDerivAt_const q (2 : ℂ)).add (hasDerivAt_id q) using 1 <;>
    simp [correctionValue]
""",
        """theorem correction_hasDerivAt (q : ℂ) :
    HasDerivAt correctionValue 1 q := by
  simpa [correctionValue] using
    (hasDerivAt_id q).const_add (2 : ℂ)
""",
        "Mock2 Advanced affine correction derivative",
    )
    m2a, count = re.subn(
        r"^theorem ([A-Za-z0-9_]+) : _ :=",
        r"noncomputable def \1 :=",
        m2a,
        flags=re.M,
    )
    if count != 601:
        raise RuntimeError(
            f"Mock2 Advanced mixed ledger aliases: expected 601 matches, found {count}"
        )
    print(f"Mock2 Advanced mixed ledger aliases: applied {count}")
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
