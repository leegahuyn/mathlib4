from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def replace_between(text: str, start: str, end: str, new: str, label: str) -> str:
    i = text.find(start)
    j = text.find(end, i)
    if i < 0 or j < 0 or text.find(start, i + 1) >= 0:
        raise RuntimeError(f"{label}: non-unique or missing markers")
    print(f"{label}: applied 1")
    return text[:i] + new + text[j:]


def replace_regex(text: str, pattern: str, repl: str, label: str, expected: int) -> str:
    text, count = re.subn(pattern, repl, text, flags=re.MULTILINE)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text


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
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_between(
        m2,
        "theorem sourceInclusion_condition (S : ShEq X) (U : Opens X) :\n",
        "/-! ### Fixed-parameter constant derived-Tor comparison model -/\n",
        EQUALIZER_BLOCK,
        "Mock2 rebuild evaluated equalizers in Type",
    )
    m2 = replace_exact(
        m2,
        """  (Proposition20ActualQGaugeSpecialization.
      proposition20ActualGlobalEquivKernel C).symm.trans
""",
        """  (Proposition20ActualQGaugeSpecialization.proposition20ActualGlobalEquivKernel C).symm.trans
""",
        "Mock2 qualify the Proposition 20 kernel equivalence",
    )
    m2 = replace_exact(
        m2,
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
        "Mock2 prove zero curvature coefficientwise",
    )
    m2 = replace_exact(
        m2,
        "theorem certificate : Certificate where",
        "noncomputable def certificate : Certificate where",
        "Mock2 make the paper-map certificate data",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem denseRange_positiveRangeToClosedL2
    (ν : GenuineHalfWeightAutomorphy.Multiplier) :
    DenseRange (positiveRangeToClosedL2 ν) := by
  change DenseRange
    (Set.inclusion (positiveL2Range ν).le_topologicalClosure)
  simpa [-SetLike.coe_sort_coe]
""",
        """theorem denseRange_positiveRangeToClosedL2
    (ν : GenuineHalfWeightAutomorphy.Multiplier) :
    DenseRange (positiveRangeToClosedL2 ν) := by
  change DenseRange
    (Set.inclusion (positiveL2Range ν).le_topologicalClosure)
  simpa [IsDenseEmbedding.subtypeEmb, Set.image_id] using
    (IsDenseEmbedding.id.subtype
      (fun x : PositiveL2Carrier => x ∈ positiveL2Range ν)).dense
""",
        "Mock2 Advanced prove positive range density in its closure",
    )
    m2a = replace_exact(
        m2a,
        """theorem denseRange_inverseRangeToClosedL2
    (ν : GenuineInverseHalfWeightAutomorphy.Multiplier) :
    DenseRange (inverseRangeToClosedL2 ν) := by
  change DenseRange
    (Set.inclusion (inverseL2Range ν).le_topologicalClosure)
  simpa [-SetLike.coe_sort_coe]
""",
        """theorem denseRange_inverseRangeToClosedL2
    (ν : GenuineInverseHalfWeightAutomorphy.Multiplier) :
    DenseRange (inverseRangeToClosedL2 ν) := by
  change DenseRange
    (Set.inclusion (inverseL2Range ν).le_topologicalClosure)
  simpa [IsDenseEmbedding.subtypeEmb, Set.image_id] using
    (IsDenseEmbedding.id.subtype
      (fun x : InverseL2Carrier => x ∈ inverseL2Range ν)).dense
""",
        "Mock2 Advanced prove inverse range density in its closure",
    )
    m2a = replace_exact(
        m2a,
        "∑ n in Finset.range N, f n",
        "∑ n ∈ Finset.range N, f n",
        "Mock2 Advanced restore current bounded-sum syntax",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """  have h :
      Tendsto (fun N => (∑' n, f n) - partialSum f N) atTop
        (𝓝 ((∑' n, f n) - (∑' n, f n))) :=
    tendsto_const_nhds.sub (partialSum_tendsto_tsum hf)
  simpa only [sub_self] using h
""",
        """  have hconst :
      Tendsto (fun _ : ℕ => ∑' n, f n) atTop (𝓝 (∑' n, f n)) :=
    tendsto_const_nhds
  have h := hconst.sub (partialSum_tendsto_tsum hf)
  simpa only [sub_self] using h
""",
        "Mock2 Advanced type the constant sequence in the remainder limit",
    )
    m2a = replace_exact(
        m2a,
        "ContDiff ℂ ∞",
        "ContDiff ℂ ⊤",
        "Mock2 Advanced use the current smoothness order",
        expected=15,
    )
    m2a = replace_exact(
        m2a,
        """  map_smul' c v := by
    ext x
    simp
""",
        """  map_smul' c v := by
    ext x
    change A (c * v) x = c * A v x
    simpa [smul_eq_mul] using
      congrArg (fun T : ℂ →L[ℂ] ℂ => T x) (A.map_smul c v)
""",
        "Mock2 Advanced prove scalar compatibility after forgetting continuity",
    )
    m2a = replace_exact(
        m2a,
        "theorem prototype_ne_zero : prototype ≠ 0 := by\n",
        """namespace Function

/-- A function is constant when all of its values agree. -/
def Constant {α β : Type*} (f : α → β) : Prop :=
  ∀ x y, f x = f y

end Function

theorem prototype_ne_zero : prototype ≠ 0 := by
""",
        "Mock2 Advanced restore the constant-function predicate",
    )
    m2a = replace_regex(
        m2a,
        r"^theorem ([A-Za-z0-9_]+)\s*:=",
        r"theorem \1 : _ :=",
        "Mock2 Advanced add inferred theorem result types",
        expected=601,
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """abbrev SobolevCompletion :=
  UniformSpace.Completion Q.GraphRange

/-- Canonical isometric embedding of the graph core into its completion. -/
""",
        """abbrev SobolevCompletion :=
  UniformSpace.Completion Q.GraphRange

/-- Use one coherent inner-product completion instance in all subsequent
completed-graph declarations. -/
noncomputable local instance sobolevCompletionInnerProductSpace :
    InnerProductSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.innerProductSpace

/-- Canonical isometric embedding of the graph core into its completion. -/
""",
        "FunctionalAnalysis install the completion inner-product instance once",
    )
    fa = replace_exact(
        fa,
        "abbrev ClosedBaseDomain :=",
        "noncomputable abbrev ClosedBaseDomain :=",
        "FunctionalAnalysis mark the completion range noncomputable",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
