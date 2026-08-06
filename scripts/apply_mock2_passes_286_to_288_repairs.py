from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def first_line(text: str) -> str:
    lines = text.splitlines()
    return lines[0] if lines else ""


def replace_exact(
    text: str,
    old: str,
    new: str,
    label: str,
    expected: int = 1,
) -> str:
    actual = text.count(old)
    print(
        f"{label}: expected={expected} actual={actual} "
        f"before={first_line(old)!r} after={first_line(new)!r}"
    )
    if actual != expected:
        raise RuntimeError(
            f"{label}: expected {expected} matches, found {actual}"
        )
    return text.replace(old, new)


def replace_between(
    text: str,
    start: str,
    end: str,
    new: str,
    label: str,
) -> str:
    start_count = text.count(start)
    end_count = text.count(end)
    print(
        f"{label}: expected_start=1 actual_start={start_count} "
        f"expected_end=1 actual_end={end_count} "
        f"before={first_line(start)!r} after={first_line(new)!r}"
    )
    if start_count != 1 or end_count != 1:
        raise RuntimeError(
            f"{label}: start matches={start_count}, end matches={end_count}"
        )
    i = text.index(start)
    j = text.index(end, i)
    return text[:i] + new + text[j:]


EQUALIZER_BLOCK = '''/-- The two evaluated restriction maps as morphisms in the category of types. -/
def sourceResInType (S : ShEq X) (U : Opens X) :
    S.ambient.Field U ⟶ S.boundary.Field U :=
  ↾(S.resIn.app U)

def sourceResOutType (S : ShEq X) (U : Opens X) :
    S.ambient.Field U ⟶ S.boundary.Field U :=
  ↾(S.resOut.app U)

theorem sourceInclusion_condition (S : ShEq X) (U : Opens X) :
    ↾(fun e : S.balancedSheaf.Field U => e.1) ≫ sourceResInType S U =
      ↾(fun e : S.balancedSheaf.Field U => e.1) ≫ sourceResOutType S U := by
  apply ConcreteCategory.hom_ext
  intro e
  exact e.2

def sourceEqualizerFork (S : ShEq X) (U : Opens X) :
    Fork (sourceResInType S U) (sourceResOutType S U) :=
  Fork.ofι (↾(fun e : S.balancedSheaf.Field U => e.1))
    (sourceInclusion_condition S U)

theorem competingFork_condition (S : ShEq X) (U : Opens X)
    (T : Fork (sourceResInType S U) (sourceResOutType S U)) (x : T.pt) :
    S.resIn.app U (T.ι x) = S.resOut.app U (T.ι x) := by
  have h := ConcreteCategory.congr_hom T.condition x
  simpa [sourceResInType, sourceResOutType] using h

def sourceEqualizerLift (S : ShEq X) (U : Opens X)
    (T : Fork (sourceResInType S U) (sourceResOutType S U)) :
    T.pt ⟶ S.balancedSheaf.Field U :=
  ↾(fun x => ⟨T.ι x, competingFork_condition S U T x⟩)

theorem sourceEqualizerLift_fac (S : ShEq X) (U : Opens X)
    (T : Fork (sourceResInType S U) (sourceResOutType S U)) :
    sourceEqualizerLift S U T ≫ (sourceEqualizerFork S U).ι = T.ι := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem sourceEqualizerLift_unique (S : ShEq X) (U : Opens X)
    (T : Fork (sourceResInType S U) (sourceResOutType S U))
    (m : T.pt ⟶ S.balancedSheaf.Field U)
    (hm : m ≫ (sourceEqualizerFork S U).ι = T.ι) :
    m = sourceEqualizerLift S U T := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom hm x
  simpa [sourceEqualizerFork] using h

def sourceEqualizerForkIsLimit (S : ShEq X) (U : Opens X) :
    IsLimit (sourceEqualizerFork S U) := by
  refine Fork.IsLimit.mk' _ fun T => ?_
  refine ⟨sourceEqualizerLift S U T, sourceEqualizerLift_fac S U T, ?_⟩
  intro m hm
  exact sourceEqualizerLift_unique S U T m hm

/-- The target fork is rebuilt from `F.obj S`; its point is the constructed
target sheaf rather than a copied profile datum. -/
def targetEqualizerFork (S : ShEq X) (U : Opens X) :
    Fork (sourceResInType S U) (sourceResOutType S U) :=
  Fork.ofι (↾(fun e : (F.obj S).sheaf.Field U => e.1))
    (sourceInclusion_condition S U)

def targetEqualizerLift (S : ShEq X) (U : Opens X)
    (T : Fork (sourceResInType S U) (sourceResOutType S U)) :
    T.pt ⟶ (F.obj S).sheaf.Field U :=
  ↾(fun x => ⟨T.ι x, competingFork_condition S U T x⟩)

theorem targetEqualizerLift_fac (S : ShEq X) (U : Opens X)
    (T : Fork (sourceResInType S U) (sourceResOutType S U)) :
    targetEqualizerLift S U T ≫ (targetEqualizerFork S U).ι = T.ι := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

theorem targetEqualizerLift_unique (S : ShEq X) (U : Opens X)
    (T : Fork (sourceResInType S U) (sourceResOutType S U))
    (m : T.pt ⟶ (F.obj S).sheaf.Field U)
    (hm : m ≫ (targetEqualizerFork S U).ι = T.ι) :
    m = targetEqualizerLift S U T := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom hm x
  simpa [targetEqualizerFork] using h

/-- The target fork has the equalizer universal property.  This is deliberately
not named `PreservesLimit`: `F` is a functor between the standalone sheaf
categories, whereas this fork lives in `Type` after evaluation at one open. -/
def targetEqualizerForkIsLimit (S : ShEq X) (U : Opens X) :
    IsLimit (targetEqualizerFork S U) := by
  refine Fork.IsLimit.mk' _ fun T => ?_
  refine ⟨targetEqualizerLift S U T, targetEqualizerLift_fac S U T, ?_⟩
  intro m hm
  exact targetEqualizerLift_unique S U T m hm

noncomputable def targetEqualizerIso (S : ShEq X) (U : Opens X) :
    (F.obj S).sheaf.Field U ≅
      equalizer (sourceResInType S U) (sourceResOutType S U) :=
  IsLimit.conePointUniqueUpToIso (targetEqualizerForkIsLimit S U)
    (limit.isLimit (parallelPair (sourceResInType S U) (sourceResOutType S U)))

'''


def main() -> int:
    text = M2.read_text(encoding="utf-8")

    # Pass 286 is already materialized in the checked-in Mock2 source.  Verify
    # that exact state rather than silently applying a duplicate replacement.
    materialized = "  sheaf : QGaugePresheaf.{u, v} (Opens X)\n"
    actual = text.count(materialized)
    print(
        "pass286 ShP universe: expected=1 "
        f"actual={actual} before='sheaf : QGaugePresheaf (Opens X)' "
        "after='sheaf : QGaugePresheaf.{u, v} (Opens X)'"
    )
    if actual != 1:
        raise RuntimeError(
            f"pass286 ShP universe: expected materialized count 1, found {actual}"
        )

    # Pass 287: rebuild the evaluated equalizers in Type and restore the actual
    # Proposition 20 / curvature / certificate declarations.
    text = replace_between(
        text,
        "theorem sourceInclusion_condition (S : ShEq X) (U : Opens X) :\n",
        "/-! ### Fixed-parameter constant derived-Tor comparison model -/\n",
        EQUALIZER_BLOCK,
        "pass287 evaluated equalizer block",
    )
    text = replace_exact(
        text,
        """  (Proposition20ActualQGaugeSpecialization.
      proposition20ActualGlobalEquivKernel C).symm.trans
""",
        """  (Proposition20ActualQGaugeSpecialization.proposition20ActualGlobalEquivKernel C).symm.trans
""",
        "pass287 qualify Proposition20 kernel equivalence",
    )
    text = replace_exact(
        text,
        """  apply LocallyConstant.ext
  intro x
  simp [qGaugeToConnection_zeroModel,
    Proposition17And18FinalSpecialization.connectionCurvature,
    Proposition17And18FinalSpecialization.curvature_apply]
""",
        """  apply LocallyConstant.ext
  intro x
  change
    PolynomialMatrixDifferentialForms.matrixDifferential
          (0 : Proposition17And18FinalSpecialization.FormFibre 1) +
        PolynomialMatrixDifferentialForms.matrixWedge
          (0 : Proposition17And18FinalSpecialization.FormFibre 1)
          (0 : Proposition17And18FinalSpecialization.FormFibre 1) = 0
  rw [PolynomialMatrixDifferentialForms.matrixDifferential_zero]
  apply Matrix.ext
  intro i j
  apply PolynomialMatrixDifferentialForms.ChartForm.ext <;>
    simp [PolynomialMatrixDifferentialForms.matrixWedge, Fin.sum_univ_two]
""",
        "pass287 prove zero curvature coefficientwise",
    )
    text = replace_exact(
        text,
        "theorem certificate : Certificate where",
        "noncomputable def certificate : Certificate where",
        "pass287 make PaperMap certificate data noncomputable",
    )

    # Pass 288: current Type-category uniqueness proofs and actual universe
    # specializations.
    text = replace_exact(
        text,
        """  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom hm x
  simpa [sourceEqualizerFork] using h
""",
        """  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change (m x).1 = T.ι x
  simpa only [CategoryTheory.comp_apply] using
    ConcreteCategory.congr_hom hm x
""",
        "pass288 source equalizer uniqueness",
    )
    text = replace_exact(
        text,
        """  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom hm x
  simpa [targetEqualizerFork] using h
""",
        """  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change (m x).1 = T.ι x
  simpa only [CategoryTheory.comp_apply] using
    ConcreteCategory.congr_hom hm x
""",
        "pass288 target equalizer uniqueness",
    )
    text = replace_exact(
        text,
        "ShEq ActualBase",
        "ShEq.{0, 0} ActualBase",
        "pass288 pin actual ShEq universes",
        expected=10,
    )
    text = replace_exact(
        text,
        """      (constantSourceTorFunctor_model (X := ActualBase) M N ≅
        F ⋙ constantTargetTorFunctor_model (X := ActualBase) M N)
""",
        """      (constantSourceTorFunctor_model.{0, 0} (X := ActualBase) M N ≅
        F.{0, 0} ⋙
          constantTargetTorFunctor_model.{0, 0} (X := ActualBase) M N)
""",
        "pass288 pin constant Tor functor universes",
    )
    text = replace_exact(
        text,
        """      (constantTorComparisonIso_model
        (X := ActualBase) M N hM).hom.app S =
""",
        """      (constantTorComparisonIso_model.{0, 0}
        (X := ActualBase) M N hM).hom.app S =
""",
        "pass288 pin comparison application universes",
    )
    text = replace_exact(
        text,
        """    ⟨constantTorComparisonIso_model (X := ActualBase) M N hM⟩
""",
        """    ⟨constantTorComparisonIso_model.{0, 0}
      (X := ActualBase) M N hM⟩
""",
        "pass288 pin comparison witness universes",
    )
    text = replace_exact(
        text,
        """    constantTorComparisonIso_model_hom_app (X := ActualBase) M N hM
""",
        """    constantTorComparisonIso_model_hom_app.{0, 0}
      (X := ActualBase) M N hM
""",
        "pass288 pin comparison theorem universes",
    )
    prefix = "Proposition20ActualQGaugeSpecialization."
    text = replace_exact(
        text,
        """  app := fun U _ => (0 : Proposition20ActualQGaugeSpecialization.Aq U)
""",
        f"""  app := fun U _ => {prefix}aqZero U
""",
        "pass288 use actual zero comparison section",
    )
    text = replace_exact(
        text,
        """    tensorToActualQGauge_zeroModel.app U s = 0 :=
""",
        f"""    tensorToActualQGauge_zeroModel.app U s = {prefix}aqZero U :=
""",
        "pass288 state zero comparison application",
    )
    text = replace_exact(
        text,
        """    (hf : ∀ (U : Opens) (s : tensorGaugePresheafOverX_zeroModel.Field U),
      f.app U s = 0) :
""",
        f"""    (hf : ∀ (U : Opens) (s : tensorGaugePresheafOverX_zeroModel.Field U),
      f.app U s = {prefix}aqZero U) :
""",
        "pass288 state zero comparison uniqueness",
    )
    text = replace_exact(
        text,
        """  ∃ (U : Opens) (s : ActualTensorGlobal),
    B.comparison.app U (B.realizeGlobal U s) ≠ 0
""",
        f"""  ∃ (U : Opens) (s : ActualTensorGlobal),
    B.comparison.app U (B.realizeGlobal U s) ≠ {prefix}aqZero U
""",
        "pass288 compare nontrivial bridge with actual zero",
    )

    M2.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
