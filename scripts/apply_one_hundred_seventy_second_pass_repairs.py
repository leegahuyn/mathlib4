from __future__ import annotations

from pathlib import Path


TARGET = Path("PrimalitySheafVerification/Mock2.lean")


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly one match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")

    text = replace_exact(
        text,
        "def mapSection {F G : Type v} (f : F → G) (U : Opens) :\n"
        "    LocallyConstant U F → LocallyConstant U G :=",
        "def mapSection {F : Type v} {G : Type w} (f : F → G) (U : Opens) :\n"
        "    LocallyConstant U F → LocallyConstant U G :=",
        "Mock2 allow locally constant section maps across fibre universes",
    )

    text = replace_exact(
        text,
        "@[simp] theorem mapSection_apply {F G : Type v} (f : F → G)\n",
        "@[simp] theorem mapSection_apply {F : Type v} {G : Type w} (f : F → G)\n",
        "Mock2 generalize locally constant map evaluation across universes",
    )

    text = replace_exact(
        text,
        "def mapMorphism {F G : Type v} (f : F → G) :\n",
        "def mapMorphism {F : Type v} {G : Type w} (f : F → G) :\n",
        "Mock2 allow induced presheaf morphisms across fibre universes",
    )

    TARGET.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
