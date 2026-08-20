from __future__ import annotations

from pathlib import Path

import apply_eighty_fourth_pass_repairs as pass84

ROOT = Path("PrimalitySheafVerification")


def restore_half_weight_semantics() -> None:
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
            "Mock2Advanced restore half-weight Sobolev semantics: "
            f"applied {count}"
        )
    elif new in block:
        print(
            "Mock2Advanced restore half-weight Sobolev semantics: already applied"
        )
    else:
        raise RuntimeError(
            "Mock2Advanced Sobolev automorphy qualification absent"
        )


def main() -> int:
    pass84.main()
    restore_half_weight_semantics()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
