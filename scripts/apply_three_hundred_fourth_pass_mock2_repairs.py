from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def first_line(text: str) -> str:
    lines = text.splitlines()
    return lines[0] if lines else ""


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    actual = text.count(old)
    print(
        f"{label}: expected={expected} actual={actual} "
        f"before={first_line(old)!r} after={first_line(new)!r}"
    )
    if actual != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {actual}")
    return text.replace(old, new)


def main() -> int:
    text = M2.read_text(encoding="utf-8")
    text = replace_exact(
        text,
        """structure StandaloneZeroProfileCertificate
    (M N : ℕ) (hM : M ≠ 0) : Type where
""",
        """structure StandaloneZeroProfileCertificate
    (M N : ℕ) (hM : M ≠ 0) : Type 1 where
""",
        "Mock2 standalone certificate universe",
    )
    text = replace_exact(
        text,
        """structure PaperElementaryConclusions
    (D : PaperElementaryInputData) (P : PaperElementaryModel D) : Type where
""",
        """structure PaperElementaryConclusions
    (D : PaperElementaryInputData) (P : PaperElementaryModel D) : Type 2 where
""",
        "Mock2 paper conclusions universe",
    )
    text = replace_exact(
        text,
        """/-- Machine-checkable certificate for the required paper map. -/
structure Certificate : Type where
""",
        """/-- Machine-checkable certificate for the required paper map. -/
structure Certificate : Type 1 where
""",
        "Mock2 PaperMap certificate universe",
    )
    text = replace_exact(
        text,
        "structure StaticAcceptanceCertificate (D : PaperElementaryInputData) : Type where",
        "structure StaticAcceptanceCertificate (D : PaperElementaryInputData) : Type 2 where",
        "Mock2 static acceptance universe",
    )
    M2.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
