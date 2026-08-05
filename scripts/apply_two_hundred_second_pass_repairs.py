from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    text = M2.read_text(encoding="utf-8")
    text = replace_exact(
        text,
        """attribute [local -instance]
  instNormedSpaceComplex_primalitySheafVerification
""",
        """attribute [-instance]
  instNormedSpaceComplex_primalitySheafVerification
""",
        "Mock2 disable the project-specific complex NormedSpace with valid syntax",
    )
    M2.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
