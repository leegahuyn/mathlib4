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
        """theorem curvature_transformPotential {U : TopologicalSpace.Opens Base}
    (g : FrameChange U) (A : Form 1 U) :
    curvatureAlgebra.curvature (g.transformPotential A) =
      g.conjugateTwo (curvatureAlgebra.curvature A) := by
  calc
    curvatureAlgebra.curvature (g.transformPotential A) =
        differential (g.transformPotential A) +
          wedge (g.transformPotential A) (g.transformPotential A) := rfl
    _ = g.conjugateTwo (differential A) +
          g.conjugateTwo (wedge A A) := g.crossTermCancellation A
    _ = g.conjugateTwo (differential A + wedge A A) :=
      (g.conjugateTwo_add (differential A) (wedge A A)).symm
    _ = g.conjugateTwo (curvatureAlgebra.curvature A) := rfl
""",
        """theorem curvature_transformPotential {U : TopologicalSpace.Opens Base}
    (g : FrameChange U) (A : Form 1 U) :
    curvatureAlgebra.curvature (g.transformPotential A) =
      g.conjugateTwo (curvatureAlgebra.curvature A) := by
  apply LocallyConstant.ext
  intro x
  change
    matrixDifferential ((g.«at» x).transformPotential (A x)) +
        matrixWedge ((g.«at» x).transformPotential (A x))
          ((g.«at» x).transformPotential (A x)) =
      (g.«at» x).conjugateTwo
        (matrixDifferential (A x) + matrixWedge (A x) (A x))
  rw [(g.«at» x).differential_transformPotential (A x),
    (g.«at» x).transformPotential_wedge_self (A x),
    (g.«at» x).conjugateOne_wedge (A x) (A x),
    (g.«at» x).conjugateTwo_add]
  abel
""",
        "Mock2 prove curvature covariance pointwise in the actual matrix DGA",
    )
    m2 = replace_exact(
        m2,
        """def connectionPresheaf : PresheafLike Base where
  Section := Proposition17And18FinalSpecialization.Connection
  res := fun U V hUV A =>
    (modularConnectionPresheaf.res hUV A.1, restrictForm hUV A.2)
""",
        """def connectionPresheaf : PresheafLike Base where
  Section := Proposition17And18FinalSpecialization.Connection
  res := fun hUV A =>
    (modularConnectionPresheaf.res hUV A.1, restrictForm hUV A.2)
""",
        "Mock2 use the dependent restriction field without rebinding open sets",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
