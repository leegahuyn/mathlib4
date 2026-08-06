from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ADVANCED = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    advanced = ADVANCED.read_text(encoding="utf-8")
    advanced = replace_exact(
        advanced,
        """/-- Use the canonical restriction-of-scalars normed-space structure consistently
throughout the real-parameter derivative calculation. -/
local instance scalarUnitaryRealNormedSpace : NormedSpace ℝ ℂ :=
  NormedSpace.complexToReal

""",
        """/-- Use Mathlib's canonical restriction-of-scalars normed-space structure
throughout the real-parameter derivative calculation. -/
""",
        "Mock2_Advanced canonical complex-to-real normed space",
    )
    ADVANCED.write_text(advanced, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
