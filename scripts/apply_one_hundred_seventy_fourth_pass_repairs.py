from __future__ import annotations

from pathlib import Path


TARGET = Path("PrimalitySheafVerification/Mock2.lean")


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly one match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")

    replacements = (
        (
            """def SectionGloballyCompatible {U : Opens} (s : (Aq D K A).Field U) : Prop :=
  ∀ x : U, GloballyCompatible D K A (s x)""",
            """def SectionGloballyCompatible {U : Opens} (s : (Aq D K A).Field U) : Prop :=
  ∀ x : U, GloballyCompatible D K A (s.toFun x)""",
            "Mock2 evaluate global compatibility through LocallyConstant.toFun",
        ),
        (
            """    apply (insideBoundary_eq_outsideBoundary_iff D K A (s x)).mp
    exact congrArg (fun t : (Bq A).Field U => t x) hs""",
            """    apply (insideBoundary_eq_outsideBoundary_iff D K A (s.toFun x)).mp
    exact congrArg (fun t : (Bq A).Field U => t.toFun x) hs""",
            "Mock2 compare equalizer boundary values through toFun",
        ),
        (
            """    exact (insideBoundary_eq_outsideBoundary_iff D K A (s x)).mpr (hs x)""",
            """    exact (insideBoundary_eq_outsideBoundary_iff D K A (s.toFun x)).mpr (hs x)""",
            "Mock2 construct equalizer membership through toFun",
        ),
    )

    for old, new, label in replacements:
        text = replace_once(text, old, new, label)

    TARGET.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
