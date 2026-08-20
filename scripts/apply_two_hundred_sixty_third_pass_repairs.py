from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


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
        """    (curvatureAlgebra.formPresheaf 2).IsGluing C
      (localCurvatureFamily C A) (connectionCurvature Aglobal) := by
  intro i
  rw [connectionCurvature_restrict]
  exact congrArg connectionCurvature (hAglobal i)
""",
        """    (curvatureAlgebra.formPresheaf 2).IsGluing C
      (localCurvatureFamily C A) (connectionCurvature Aglobal) := by
  intro i
  change
    restrictForm (C.piece_le_target i)
        (curvatureAlgebra.curvature Aglobal.2) =
      curvatureAlgebra.curvature (A i).2
  rw [curvatureAlgebra.curvature_restrict]
  exact congrArg curvatureAlgebra.curvature
    (congrArg Prod.snd (hAglobal i))
""",
        "Mock2 unfold final connection sections before curvature restriction",
    )
    m2 = replace_exact(
        m2,
        """theorem zeroGlobalConnection_isFlat : IsFlat zeroGlobalConnection := by
  apply LocallyConstant.ext
  intro x
  simp [IsFlat, curvatureForm, zeroGlobalConnection,
    Proposition17And18FinalSpecialization.zeroConnection,
    Proposition17And18FinalSpecialization.connectionCurvature,
    Proposition17And18FinalSpecialization.curvature_apply]
""",
        """theorem zeroGlobalConnection_isFlat : IsFlat zeroGlobalConnection := by
  apply LocallyConstant.ext
  intro x
  change
    matrixDifferential (0 : FormFibre 1) +
        matrixWedge (0 : FormFibre 1) (0 : FormFibre 1) = 0
  rw [matrixDifferential_zero]
  simp [matrixWedge, Fin.sum_univ_two]
""",
        "Mock2 prove zero curvature in the concrete matrix DGA",
    )
    m2 = replace_exact(
        m2,
        """def aqAdd (U : Opens) (A B : Aq U) : Aq U :=
  ⟨A.1 + B.1,
    Definition15Geometry.equation62_add
""",
        """def aqAdd (U : Opens) (A B : Aq U) : Aq U :=
  ⟨Definition15Geometry.SmoothOneForm.add
      GaugeModel GaugeGroup U A.1 B.1,
    Definition15Geometry.equation62_add
""",
        "Mock2 define q-gauge addition through the concrete smooth-one-form operation",
    )
    m2 = replace_exact(
        m2,
        """def aqNeg (U : Opens) (A : Aq U) : Aq U :=
  ⟨-A.1,
    Definition15Geometry.equation62_neg
""",
        """def aqNeg (U : Opens) (A : Aq U) : Aq U :=
  ⟨Definition15Geometry.SmoothOneForm.neg
      GaugeModel GaugeGroup U A.1,
    Definition15Geometry.equation62_neg
""",
        "Mock2 define q-gauge negation through the concrete smooth-one-form operation",
    )
    m2 = replace_exact(
        m2,
        """instance aqSectionAddCommGroup (U : Opens) : AddCommGroup (Aq U) where
  zero := aqZero U
  add := aqAdd U
  neg := aqNeg U
  nsmul := @nsmulRec (Aq U) ⟨aqZero U⟩ ⟨aqAdd U⟩
  zsmul := @zsmulRec (Aq U) ⟨aqZero U⟩ ⟨aqAdd U⟩ ⟨aqNeg U⟩
    (@nsmulRec (Aq U) ⟨aqZero U⟩ ⟨aqAdd U⟩)
  add_zero A := by
    apply Subtype.ext
    exact add_zero A.1
  zero_add A := by
    apply Subtype.ext
    exact zero_add A.1
  add_comm A B := by
    apply Subtype.ext
    exact add_comm A.1 B.1
  add_assoc A B D := by
    apply Subtype.ext
    exact add_assoc A.1 B.1 D.1
  neg_add_cancel A := by
    apply Subtype.ext
    exact neg_add_cancel A.1

@[simp] theorem aqAdd_val (U : Opens) (A B : Aq U) :
    (A + B).1 = A.1 + B.1 := rfl

@[simp] theorem aqNeg_val (U : Opens) (A : Aq U) :
    (-A).1 = -A.1 := rfl

@[simp] theorem aqZero_val (U : Opens) :
    (0 : Aq U).1 = 0 := rfl
""",
        """instance aqSectionAddCommGroup (U : Opens) : AddCommGroup (Aq U) where
  zero := aqZero U
  add := aqAdd U
  neg := aqNeg U
  nsmul := @nsmulRec (Aq U) ⟨aqZero U⟩ ⟨aqAdd U⟩
  zsmul := @zsmulRec (Aq U) ⟨aqZero U⟩ ⟨aqAdd U⟩ ⟨aqNeg U⟩
    (@nsmulRec (Aq U) ⟨aqZero U⟩ ⟨aqAdd U⟩)
  add_zero A := by
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

@[simp] theorem aqAdd_val (U : Opens) (A B : Aq U) :
    (A + B).1 = Definition15Geometry.SmoothOneForm.add
      GaugeModel GaugeGroup U A.1 B.1 := rfl

@[simp] theorem aqNeg_val (U : Opens) (A : Aq U) :
    (-A).1 = Definition15Geometry.SmoothOneForm.neg
      GaugeModel GaugeGroup U A.1 := rfl

@[simp] theorem aqZero_val (U : Opens) :
    (0 : Aq U).1 = Definition15Geometry.SmoothOneForm.zero
      GaugeModel GaugeGroup U := rfl
""",
        "Mock2 construct the q-gauge additive group without unfolding presheaf aliases",
    )
    m2 = replace_exact(
        m2,
        """theorem aqRes_add {V U : Opens} (hVU : V ≤ U) (A B : Aq U) :
    AqPresheaf.res hVU (A + B) =
      AqPresheaf.res hVU A + AqPresheaf.res hVU B := by
  apply Subtype.ext
  exact Definition15Geometry.SmoothOneForm.restrict_add
    GaugeModel GaugeGroup hVU A.1 B.1
""",
        """theorem aqRes_add {V U : Opens} (hVU : V ≤ U) (A B : Aq U) :
    AqPresheaf.res hVU (A + B) =
      AqPresheaf.res hVU A + AqPresheaf.res hVU B := by
  apply Subtype.ext
  apply Definition15Geometry.SmoothOneForm.ext_pointwise
  intro τ
  rfl
""",
        "Mock2 prove q-gauge restriction additivity pointwise",
    )
    m2 = replace_exact(
        m2,
        """theorem aqRes_neg {V U : Opens} (hVU : V ≤ U) (A : Aq U) :
    AqPresheaf.res hVU (-A) = -AqPresheaf.res hVU A := by
  apply Subtype.ext
  exact Definition15Geometry.SmoothOneForm.restrict_neg
    GaugeModel GaugeGroup hVU A.1
""",
        """theorem aqRes_neg {V U : Opens} (hVU : V ≤ U) (A : Aq U) :
    AqPresheaf.res hVU (-A) = -AqPresheaf.res hVU A := by
  apply Subtype.ext
  apply Definition15Geometry.SmoothOneForm.ext_pointwise
  intro τ
  rfl
""",
        "Mock2 prove q-gauge restriction negation pointwise",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  · simp [cuspFiniteAmbientTangent, cuspHorizontalAmbientCurve, neg_sq]
""",
        """  · ring
""",
        "Mock2 Advanced close the finite-cusp reciprocal square in normal form",
    )
    m2a = replace_exact(
        m2a,
        """  field_simp [hτ]
  rw [sub_eq_add_neg]
""",
        """  field_simp [hτ]
  ring
""",
        "Mock2 Advanced close the base product after denominator clearing",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
