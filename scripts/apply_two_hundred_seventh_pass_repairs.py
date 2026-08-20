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
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """attribute [-instance]
  instNormedSpaceComplex_primalitySheafVerification
""",
        """local instance (priority := 2000) : NormedSpace ℂ ℂ :=
  (RCLike.innerProductSpace : InnerProductSpace ℂ ℂ).toNormedSpace
""",
        "Mock2 derive the canonical complex NormedSpace from RCLike.innerProductSpace",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
