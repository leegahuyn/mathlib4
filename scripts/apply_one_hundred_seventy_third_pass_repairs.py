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
            """@[simp] theorem resIn_apply (U : Opens) (s : (Aq D K A).Field U)
    (x : U) :
    (resIn D K A).app U s x = insideBoundaryDatum D K A (s x) :=
  rfl""",
            """@[simp] theorem resIn_apply (U : Opens) (s : (Aq D K A).Field U)
    (x : U) :
    ((resIn D K A).app U s).toFun x =
      insideBoundaryDatum D K A (s.toFun x) :=
  rfl""",
            "Mock2 evaluate resIn through LocallyConstant.toFun",
        ),
        (
            """@[simp] theorem resOut_apply (U : Opens) (s : (Aq D K A).Field U)
    (x : U) :
    (resOut D K A).app U s x = outsideBoundaryDatum D K A (s x) :=
  rfl""",
            """@[simp] theorem resOut_apply (U : Opens) (s : (Aq D K A).Field U)
    (x : U) :
    ((resOut D K A).app U s).toFun x =
      outsideBoundaryDatum D K A (s.toFun x) :=
  rfl""",
            "Mock2 evaluate resOut through LocallyConstant.toFun",
        ),
        (
            """    ((resIn D K A).app U s x).inside q =
      (s x).mockPart.1.series.inside.sumAt q.1 :=""",
            """    (((resIn D K A).app U s).toFun x).inside q =
      (s.toFun x).mockPart.1.series.inside.sumAt q.1 :=""",
            "Mock2 evaluate resIn inside component through toFun",
        ),
        (
            """    ((resIn D K A).app U s x).outside q =
      (s x).mockPart.1.series.inside.sumAt q.1 :=""",
            """    (((resIn D K A).app U s).toFun x).outside q =
      (s.toFun x).mockPart.1.series.inside.sumAt q.1 :=""",
            "Mock2 evaluate resIn outside component through toFun",
        ),
        (
            """    ((resOut D K A).app U s x).inside q =
      (2 : ℂ) * K.psi.sumAt q.1 -
        (s x).mockPart.1.series.correction.sumAt q.1 :=""",
            """    (((resOut D K A).app U s).toFun x).inside q =
      (2 : ℂ) * K.psi.sumAt q.1 -
        (s.toFun x).mockPart.1.series.correction.sumAt q.1 :=""",
            "Mock2 evaluate resOut inside component through toFun",
        ),
        (
            """    ((resOut D K A).app U s x).outside q =
      (s x).mockPart.1.series.outside.sumAt q.1⁻¹ :=""",
            """    (((resOut D K A).app U s).toFun x).outside q =
      (s.toFun x).mockPart.1.series.outside.sumAt q.1⁻¹ :=""",
            "Mock2 evaluate resOut outside component through toFun",
        ),
        (
            """    ((resOut D K A).app U s x).inside q =
      ((resOut D K A).app U s x).outside q :=
  outsideBoundaryDatum_components_eq D K A (s x) q""",
            """    (((resOut D K A).app U s).toFun x).inside q =
      (((resOut D K A).app U s).toFun x).outside q :=
  outsideBoundaryDatum_components_eq D K A (s.toFun x) q""",
            "Mock2 evaluate resOut component equality through toFun",
        ),
    )

    for old, new, label in replacements:
        text = replace_once(text, old, new, label)

    TARGET.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
