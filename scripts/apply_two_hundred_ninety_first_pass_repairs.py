from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  add_mem' := by
    intro A B hA hB
    change ContDiff ℂ ⊤ (fun z => A z + B z)
    exact hA.add hB
  smul_mem' := by
    intro c A hA
    change ContDiff ℂ ⊤ (fun z => c • A z)
    exact hA.const_smul c
""",
        """  add_mem' := by
    intro A B hA hB
    change ContDiff ℂ ⊤ A at hA
    change ContDiff ℂ ⊤ B at hB
    change ContDiff ℂ ⊤ (fun z => A z + B z)
    exact hA.add hB
  smul_mem' := by
    intro c A hA
    change ContDiff ℂ ⊤ A at hA
    change ContDiff ℂ ⊤ (fun z => c • A z)
    exact hA.const_smul c
""",
        "Mock2 Advanced expose continuous smoothness hypotheses",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_scalarUnitaryScattering (t : ℝ) :
    HasDerivAt scalarUnitaryScattering (scalarUnitaryDerivative t) t := by
  have hinner :
      HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I (t : ℂ) :=
    hasDerivAt_const_mul Complex.I
  have hcomplex :
      HasDerivAt
        (fun z : ℂ => Complex.exp (Complex.I * z))
        (Complex.I * Complex.exp (Complex.I * (t : ℂ))) (t : ℂ) := by
    simpa only [mul_comm] using
      (Complex.hasDerivAt_exp (Complex.I * (t : ℂ))).comp (t : ℂ) hinner
  simpa only [scalarUnitaryScattering, scalarUnitaryDerivative] using
    hcomplex.comp_ofReal
""",
        """theorem hasDerivAt_scalarUnitaryScattering (t : ℝ) :
    HasDerivAt scalarUnitaryScattering (scalarUnitaryDerivative t) t := by
  have hinner :
      HasDerivAt (fun z : ℂ => Complex.I * z) Complex.I (t : ℂ) :=
    hasDerivAt_const_mul Complex.I
  have hcomplex := hinner.cexp
  simpa [scalarUnitaryScattering, scalarUnitaryDerivative, mul_comm] using
    hcomplex.comp_ofReal
""",
        "Mock2 Advanced prove the unitary exponential derivative through cexp",
    )
    m2a = replace_exact(
        m2a,
        """theorem correction_hasDerivAt (q : ℂ) :
    HasDerivAt correctionValue 1 q := by
  simpa [correctionValue] using
    (hasDerivAt_const q (2 : ℂ)).add (hasDerivAt_id q)
""",
        """theorem correction_hasDerivAt (q : ℂ) :
    HasDerivAt correctionValue 1 q := by
  convert (hasDerivAt_const q (2 : ℂ)).add (hasDerivAt_id q) using 1 <;>
    simp [correctionValue]
""",
        "Mock2 Advanced normalize the affine correction derivative",
    )
    m2a = replace_exact(
        m2a,
        """theorem prototype_differentiable : Differentiable ℂ prototype := by
  simpa [prototype] using
    (differentiable_id.add (differentiable_const (1 : ℂ)))
""",
        """theorem prototype_differentiable : Differentiable ℂ prototype := by
  unfold prototype
  fun_prop
""",
        "Mock2 Advanced prove affine prototype differentiability",
    )
    m2a = replace_exact(
        m2a,
        """theorem dependencies_nonempty (c : Claim) :
    (dependencies c).Nonempty := by
  cases c <;> simp [dependencies]
""",
        """theorem dependencies_nonempty (c : Claim) :
    dependencies c ≠ [] := by
  cases c <;> simp [dependencies]
""",
        "Mock2 Advanced express nonempty dependency lists with current List API",
    )
    m2a, count = re.subn(
        r"^theorem ([A-Za-z0-9_]+) :=",
        r"theorem \1 : _ :=",
        m2a,
        flags=re.M,
    )
    if count != 601:
        raise RuntimeError(
            f"Mock2 Advanced inferred theorem aliases: expected 601 matches, found {count}"
        )
    print(f"Mock2 Advanced inferred theorem aliases: applied {count}")
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """/-- Keep one coherent scalar and inner-product structure on the completion for
all subsequent bundled maps. -/
noncomputable local instance sobolevCompletionNormedSpace :
    NormedSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange

noncomputable local instance sobolevCompletionInnerProductSpace :
    InnerProductSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.innerProductSpace

""",
        "",
        "FunctionalAnalysis restore the canonical completion instances",
    )
    fa = replace_exact(
        fa,
        """@[simp]
theorem completionEnergyOperator_apply (u v : Q.SobolevCompletion) :
    Q.completionEnergyOperator u v = ⟪v, u⟫_ℂ :=
  innerSLFlip_apply_apply ℂ u v
""",
        """@[simp]
theorem completionEnergyOperator_apply (u v : Q.SobolevCompletion) :
    Q.completionEnergyOperator u v = ⟪v, u⟫_ℂ := by
  simpa [completionEnergyOperator] using
    (innerSLFlip_apply_apply ℂ u v)
""",
        "FunctionalAnalysis unfold the canonical completion energy operator",
    )
    fa = replace_exact(
        fa,
        """  rw [Q.completionEnergyOperator_apply]
  change ⟪Q.coreEmbedding (Q.toGraphRange v),
      Q.coreEmbedding (Q.toGraphRange u)⟫_ℂ = Q.energyForm v u
  rw [Q.coreEmbedding.inner_map_map, Q.inner_toGraphRange]
""",
        """  rw [Q.completionEnergyOperator_apply]
  change ⟪Q.coreEmbedding (Q.toGraphRange v),
      Q.coreEmbedding (Q.toGraphRange u)⟫_ℂ = Q.energyForm v u
  exact (Q.coreEmbedding.inner_map_map _ _).trans
    (Q.inner_toGraphRange v u)
""",
        "FunctionalAnalysis transport the dense-core pairing directly",
    )
    fa = replace_exact(
        fa,
        """theorem completionEnergyOperator_self_eq_zero_iff (u : Q.SobolevCompletion) :
    Q.completionEnergyOperator u u = 0 ↔ u = 0 := by
  rw [Q.completionEnergyOperator_apply, inner_self_eq_zero]
""",
        """theorem completionEnergyOperator_self_eq_zero_iff (u : Q.SobolevCompletion) :
    Q.completionEnergyOperator u u = 0 ↔ u = 0 := by
  rw [Q.completionEnergyOperator_apply]
  exact inner_self_eq_zero
""",
        "FunctionalAnalysis prove the completed pairing zero criterion",
    )
    fa = replace_exact(
        fa,
        """  refine ⟨zero_lt_one, fun u ↦ ?_⟩
  rw [one_mul, Q.completionEnergyOperator_apply,
    inner_self_eq_norm_sq]
""",
        """  refine ⟨zero_lt_one, fun u ↦ ?_⟩
  rw [one_mul, Q.completionEnergyOperator_apply]
  exact le_of_eq (norm_sq_eq_re_inner (𝕜 := ℂ) u)
""",
        "FunctionalAnalysis prove sharp completion coercivity by the norm identity",
    )
    fa = replace_exact(
        fa,
        """abbrev ClosedBaseDomain :=
  LinearMap.range Q.baseExtension.toLinearMap
""",
        """noncomputable def ClosedBaseDomain :=
  LinearMap.range Q.baseExtension.toLinearMap
""",
        "FunctionalAnalysis mark the closed base range noncomputable",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
