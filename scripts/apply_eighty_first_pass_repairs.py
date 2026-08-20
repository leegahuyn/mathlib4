from __future__ import annotations

from pathlib import Path

import apply_eightieth_pass_repairs as pass80

ROOT = Path("PrimalitySheafVerification")


def repair_mock2_advanced_semantics() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")

    start = text.index("namespace GenuineWeightedSobolev")
    end = text.index("end GenuineWeightedSobolev", start)
    block = text[start:end]

    old = "GenuineInverseHalfWeightAutomorphy."
    new = "GenuineHalfWeightAutomorphy."
    count = block.count(old)
    if count:
        block = block.replace(old, new)
        text = text[:start] + block + text[end:]
        path.write_text(text, encoding="utf-8", newline="\n")
        print(
            "Mock2Advanced preserve the half-weight Sobolev convention: "
            f"applied {count}"
        )
    elif new in block:
        print(
            "Mock2Advanced preserve the half-weight Sobolev convention: "
            "already applied"
        )
    else:
        raise RuntimeError(
            "Mock2Advanced weighted Sobolev automorphy qualification absent"
        )


def main() -> int:
    pass80.main()
    repair_mock2_advanced_semantics()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
