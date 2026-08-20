from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MOCK2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 occurrence, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    text = MOCK2.read_text(encoding="utf-8")
    text = replace_once(
        text,
        "def modularCovariantAqPresheaf (MC : AqTop.ModularCovarianceData)\n",
        "noncomputable def modularCovariantAqPresheaf (MC : AqTop.ModularCovarianceData)\n",
        "Mock2 propagate AqPresheaf noncomputability to modularCovariantAqPresheaf",
    )
    MOCK2.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
