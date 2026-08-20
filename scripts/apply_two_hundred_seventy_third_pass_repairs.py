from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """def equation613LeftType : LocalFamily C ⟶ OverlapFamily C := by
  change LocalFamily C → OverlapFamily C
  exact fun s => equation613Left C s

/-- Underlying Type-valued morphism of the right overlap map. -/
def equation613RightType : LocalFamily C ⟶ OverlapFamily C := by
  change LocalFamily C → OverlapFamily C
  exact fun s => equation613Right C s
""",
        """def equation613LeftType : LocalFamily C ⟶ OverlapFamily C :=
  as_hom (fun s : LocalFamily C => equation613Left C s)

/-- Underlying Type-valued morphism of the right overlap map. -/
def equation613RightType : LocalFamily C ⟶ OverlapFamily C :=
  as_hom (fun s : LocalFamily C => equation613Right C s)
""",
        "Mock2 guide the equation 6.13 functions into Type morphisms",
    )
    m2 = replace_exact(
        m2,
        """    (fun e : AqPresheaf.CoverEqualizer C.openCover => e.1) ≫
        (equation613LeftType C) =
      (fun e : AqPresheaf.CoverEqualizer C.openCover => e.1) ≫
        (equation613RightType C) := by
""",
        """    as_hom (fun e : AqPresheaf.CoverEqualizer C.openCover => e.1) ≫
        (equation613LeftType C) =
      as_hom (fun e : AqPresheaf.CoverEqualizer C.openCover => e.1) ≫
        (equation613RightType C) := by
""",
        "Mock2 guide the equalizer subtype inclusion into Type",
    )
    m2 = replace_exact(
        m2,
        """  Fork.ofι (fun e : AqPresheaf.CoverEqualizer C.openCover => e.1)
    (categoricalInclusion_condition C)
""",
        """  Fork.ofι (as_hom (fun e : AqPresheaf.CoverEqualizer C.openCover => e.1))
    (categoricalInclusion_condition C)
""",
        "Mock2 construct the subtype fork with an explicit Type morphism",
    )
    m2 = replace_exact(
        m2,
        """    S.pt ⟶ AqPresheaf.CoverEqualizer C.openCover :=
  fun x => ⟨S.ι x, competingFork_condition C S x⟩
""",
        """    S.pt ⟶ AqPresheaf.CoverEqualizer C.openCover :=
  as_hom (fun x => ⟨S.ι x, competingFork_condition C S x⟩)
""",
        "Mock2 guide the categorical lift into Type",
    )
    m2 = replace_exact(
        m2,
        """    (fun A : Aq (⊤ : Opens) => AqPresheaf.restrictToCover C.openCover A) ≫
        (equation613LeftType C) =
      (fun A : Aq (⊤ : Opens) => AqPresheaf.restrictToCover C.openCover A) ≫
        (equation613RightType C) := by
""",
        """    as_hom (fun A : Aq (⊤ : Opens) => AqPresheaf.restrictToCover C.openCover A) ≫
        (equation613LeftType C) =
      as_hom (fun A : Aq (⊤ : Opens) => AqPresheaf.restrictToCover C.openCover A) ≫
        (equation613RightType C) := by
""",
        "Mock2 guide global restriction into Type",
    )
    m2 = replace_exact(
        m2,
        """  Fork.ofι
    (fun A : Aq (⊤ : Opens) => AqPresheaf.restrictToCover C.openCover A)
    (globalRestriction_condition C)
""",
        """  Fork.ofι
    (as_hom (fun A : Aq (⊤ : Opens) => AqPresheaf.restrictToCover C.openCover A))
    (globalRestriction_condition C)
""",
        "Mock2 construct the global restriction fork in Type",
    )
    m2 = replace_exact(
        m2,
        """    S.pt ⟶ Aq (⊤ : Opens) :=
  fun x => (proposition20ActualGlobalEquivEqualizer C).symm
    (categoricalLift C S x)
""",
        """    S.pt ⟶ Aq (⊤ : Opens) :=
  as_hom (fun x => (proposition20ActualGlobalEquivEqualizer C).symm
    (categoricalLift C S x))
""",
        "Mock2 guide the global categorical lift into Type",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
