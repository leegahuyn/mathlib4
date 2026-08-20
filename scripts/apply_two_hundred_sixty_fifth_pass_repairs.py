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
        """  intro i
  change
    restrictForm (C.piece_le_target i)
        (curvatureAlgebra.curvature Aglobal.2) =
      curvatureAlgebra.curvature (A i).2
  rw [curvatureAlgebra.curvature_restrict]
  exact congrArg curvatureAlgebra.curvature
    (congrArg Prod.snd (hAglobal i))
""",
        """  intro i
  exact
    (connectionCurvature_restrict (C.piece_le_target i) Aglobal).trans
      (congrArg connectionCurvature (hAglobal i))
""",
        "Mock2 compose curvature restriction and gluing without unfolding opaque sections",
    )
    m2 = replace_exact(
        m2,
        """  change
    matrixDifferential (0 : FormFibre 1) +
        matrixWedge (0 : FormFibre 1) (0 : FormFibre 1) = 0
  rw [matrixDifferential_zero]
  simp [matrixWedge, Fin.sum_univ_two]
""",
        """  change
    PolynomialMatrixDifferentialForms.matrixDifferential
          (0 : FormFibre 1) +
        PolynomialMatrixDifferentialForms.matrixWedge
          (0 : FormFibre 1) (0 : FormFibre 1) = 0
  rw [PolynomialMatrixDifferentialForms.matrixDifferential_zero]
  simp [PolynomialMatrixDifferentialForms.matrixWedge, Fin.sum_univ_two]
""",
        "Mock2 qualify the concrete matrix DGA operations in zero curvature",
    )
    m2 = replace_exact(
        m2,
        """  add_zero A := by
    apply Subtype.ext
    apply Definition15Geometry.SmoothOneForm.ext_pointwise
    intro τ
    exact add_zero (A.1 τ)
  zero_add A := by
    apply Subtype.ext
    apply Definition15Geometry.SmoothOneForm.ext_pointwise
    intro τ
    exact zero_add (A.1 τ)
  add_comm A B := by
    apply Subtype.ext
    apply Definition15Geometry.SmoothOneForm.ext_pointwise
    intro τ
    exact add_comm (A.1 τ) (B.1 τ)
  add_assoc A B D := by
    apply Subtype.ext
    apply Definition15Geometry.SmoothOneForm.ext_pointwise
    intro τ
    exact add_assoc (A.1 τ) (B.1 τ) (D.1 τ)
  neg_add_cancel A := by
    apply Subtype.ext
    apply Definition15Geometry.SmoothOneForm.ext_pointwise
    intro τ
    exact neg_add_cancel (A.1 τ)
""",
        """  add_zero A := by
    apply Subtype.ext
    change Definition15Geometry.SmoothOneForm.add
        GaugeModel GaugeGroup U A.1
          (Definition15Geometry.SmoothOneForm.zero GaugeModel GaugeGroup U) = A.1
    exact add_zero
      (show Definition15Geometry.SmoothOneForm GaugeModel GaugeGroup U from A.1)
  zero_add A := by
    apply Subtype.ext
    change Definition15Geometry.SmoothOneForm.add
        GaugeModel GaugeGroup U
          (Definition15Geometry.SmoothOneForm.zero GaugeModel GaugeGroup U) A.1 = A.1
    exact zero_add
      (show Definition15Geometry.SmoothOneForm GaugeModel GaugeGroup U from A.1)
  add_comm A B := by
    apply Subtype.ext
    change Definition15Geometry.SmoothOneForm.add
        GaugeModel GaugeGroup U A.1 B.1 =
      Definition15Geometry.SmoothOneForm.add GaugeModel GaugeGroup U B.1 A.1
    exact add_comm
      (show Definition15Geometry.SmoothOneForm GaugeModel GaugeGroup U from A.1)
      (show Definition15Geometry.SmoothOneForm GaugeModel GaugeGroup U from B.1)
  add_assoc A B D := by
    apply Subtype.ext
    change Definition15Geometry.SmoothOneForm.add GaugeModel GaugeGroup U
        (Definition15Geometry.SmoothOneForm.add GaugeModel GaugeGroup U A.1 B.1) D.1 =
      Definition15Geometry.SmoothOneForm.add GaugeModel GaugeGroup U A.1
        (Definition15Geometry.SmoothOneForm.add GaugeModel GaugeGroup U B.1 D.1)
    exact add_assoc
      (show Definition15Geometry.SmoothOneForm GaugeModel GaugeGroup U from A.1)
      (show Definition15Geometry.SmoothOneForm GaugeModel GaugeGroup U from B.1)
      (show Definition15Geometry.SmoothOneForm GaugeModel GaugeGroup U from D.1)
  neg_add_cancel A := by
    apply Subtype.ext
    change Definition15Geometry.SmoothOneForm.add GaugeModel GaugeGroup U
        (Definition15Geometry.SmoothOneForm.neg GaugeModel GaugeGroup U A.1) A.1 =
      Definition15Geometry.SmoothOneForm.zero GaugeModel GaugeGroup U
    exact neg_add_cancel
      (show Definition15Geometry.SmoothOneForm GaugeModel GaugeGroup U from A.1)
""",
        "Mock2 prove q-gauge additive laws in the explicit smooth-one-form carrier",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
