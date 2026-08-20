from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        raise RuntimeError(f"{label}: expected block not found")
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = "theorem sectionOf_objectSchema_at\n"
    end = "end AdvancedClaimsIIRequirement\n"
    starts = [i for i in range(len(text)) if text.startswith(start, i)]
    if len(starts) == 2:
        first_start, second_start = starts
        first_end = text.index(end, first_start)
        helper_start = text.rfind("private theorem mem_all_aux", first_end, second_start)
        second_end = text.index(end, second_start)
        if helper_start < 0:
            raise RuntimeError("Mock1Advanced repaired registry helper not found")
        repaired_block = text[helper_start:second_end]
        text = text[:first_start] + repaired_block + text[first_end:]
        changed = True
        print("Mock1Advanced copy the kernel-checked registry proof to the first duplicate block: applied")
    elif len(starts) == 1 and text.count("private theorem mem_all_aux") >= 2:
        print("Mock1Advanced first duplicate registry block: already repaired")
    else:
        raise RuntimeError(
            f"Mock1Advanced expected two registry blocks before repair, found {len(starts)}"
        )

    old = """theorem object_schema_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    PaperDataInstancePayloadCertificate.paper_object_instance_at
        C.paperDataInstancePayload /\\
      forall n, PaperDataInstancePayloadCertificate.scalar_jacobi_at
        C.paperDataInstancePayload n :=
  And.intro A.paper_object_data_instance A.scalar_jacobi_degeneracy
"""
    new = """theorem object_schema_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    (C.paperInstance.extraction.concrete = C.paperInstance.namedInstance.concrete /\\
      C.paperInstance.family = C.paperInstance.namedInstance.family /\\
        C.paperInstance.family.objectName = referenceMock1DepthOneObjectName /\\
          C.paperInstance.family.familyName = referenceMock1DepthOneFamilyName /\\
            Not (C.paperInstance.family.sourceName = \"\")) /\\
      (forall n, C.advanced.degeneracyRelation.jacobiCoeff n
        C.advanced.degeneracyRelation.ellStar =
          C.advanced.degeneracyRelation.scalarCoeff n) :=
  And.intro A.paper_object_data_instance A.scalar_jacobi_degeneracy
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced restore the object-schema audit accessor proposition")
    changed |= did

    old = """theorem t1t5_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    PaperDataInstancePayloadCertificate.appell_lerch_at
        C.paperDataInstancePayload /\\
      PaperDataInstancePayloadCertificate.principal_exponent_at
          C.paperDataInstancePayload /\\
        PaperDataInstancePayloadCertificate.matrix_solution_at
            C.paperDataInstancePayload /\\
          PaperDataInstancePayloadCertificate.fixed_shadow_at
              C.paperDataInstancePayload /\\
            forall n, PaperDataInstancePayloadCertificate.inside_outside_at
              C.paperDataInstancePayload n :=
  And.intro A.appell_lerch_block_formula
    (And.intro A.principal_exponent_formula
      (And.intro A.paper_matrix_rhs_solution
        (And.intro A.fixed_shadow_unary_theta_data
          A.inside_outside_qseries)))
"""
    new = """theorem t1t5_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    (List.Mem C.advanced.appellLerch.m referenceMock1MList /\\
      List.Mem C.advanced.appellLerch.r referenceMock1RPhases /\\
        C.advanced.appellLerch.uTauCoeff - C.advanced.appellLerch.vTauCoeff = 0 /\\
          C.advanced.appellLerch.uConst - C.advanced.appellLerch.vConst =
            C.advanced.appellLerch.z0) /\\
      (C.advanced.exponentFormula.exponent =
          paperPrincipalExponent C.advanced.exponentFormula.n
            C.advanced.exponentFormula.ell C.advanced.exponentFormula.m /\\
        C.advanced.exponentFormula.exponent < 0) /\\
        MatVecRat C.advanced.rationalSolve.matrix C.advanced.rationalSolve.solution =
          C.advanced.rationalSolve.rhs /\\
          (Not (C.advanced.fixedShadow.thetaSymbol = \"\") /\\
            C.advanced.fixedShadow.z0 = (-1 / 2 : Rat) /\\
              C.advanced.fixedShadow.nonzeroCase /\\
                Not (C.advanced.fixedShadow.scale = 0)) /\\
            (forall n, C.advanced.insideOutside.inside.coeff n =
                C.advanced.insideOutside.outside.coeff n /\\
              C.advanced.insideOutside.outside.coeff n =
                C.advanced.insideOutside.partialTheta.coeff n -
                  C.advanced.insideOutside.correction.coeff n) :=
  And.intro A.appell_lerch_block_formula
    (And.intro A.principal_exponent_formula
      (And.intro A.paper_matrix_rhs_solution
        (And.intro A.fixed_shadow_unary_theta_data
          A.inside_outside_qseries)))
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced restore the T1-T5 audit accessor propositions")
    changed |= did

    old = """theorem kernel_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    SPTKernelRequirementPayloadCertificate.valuation_certificate_at
        C.sptKernelRequirementPayload /\\
      SPTKernelRequirementPayloadCertificate.kernel_table_at
          C.sptKernelRequirementPayload /\\
        SPTKernelRequirementPayloadCertificate.multiplier_input_at
            C.sptKernelRequirementPayload /\\
          SPTKernelRequirementPayloadCertificate.cusp_input_at
            C.sptKernelRequirementPayload :=
  And.intro A.actual_mpk_valuation_certificate
    (And.intro A.kernel_selection_table_input
      (And.intro A.multiplier_phase_matching_input
        A.cusp_convergence_proof_data))
"""
    new = """theorem kernel_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    (Nat.Prime C.sptKernel.sptFree.valuation.p /\\
      C.sptKernel.sptFree.valuation.p ^ C.sptKernel.sptFree.valuation.vp ∣
        C.sptKernel.sptFree.valuation.M /\\
      Not (C.sptKernel.sptFree.valuation.p ^
        (C.sptKernel.sptFree.valuation.vp + 1) ∣
          C.sptKernel.sptFree.valuation.M)) /\\
      (Not (C.sptKernel.kernelSelection.sourceName = \"\") /\\
        C.sptKernel.kernelSelection.selectedModulus =
          C.sptKernel.kernelSelection.level /\\
        C.sptKernel.kernelSelection.multiplierRows.length =
          C.sptKernel.kernelSelection.level) /\\
      (C.sptKernel.multiplier.ts = C.sptKernel.kernelCusp.phaseMatching /\\
        C.sptKernel.multiplier.rows.length = 2) /\\
      (C.sptKernel.cuspConvergence.boundary =
          C.sptKernel.kernelCusp.convergence /\\
        C.sptKernel.cuspConvergence.boundary.passes = true) :=
  And.intro A.actual_mpk_valuation_certificate
    (And.intro A.kernel_selection_table_input
      (And.intro A.multiplier_phase_matching_input
        A.cusp_convergence_proof_data))
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced restore the kernel audit accessor propositions")
    changed |= did

    old = """theorem exact_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    ExactCoefficientRequirementPayloadCertificate.paper_formula_fields_at
      C.exactCoefficientRequirementPayload :=
  A.paper_data_formula_proof_fields
"""
    new = """theorem exact_actual_inputs_at
    {C : AdvancedClaimsIICompletionCertificate}
    (A : AdvancedClaimsIIActualInputAuditCertificate C) :
    (forall r : ExactCoefficientERequirement, List.Mem r C.exact.requirements) /\\
      (forall n, C.betaArch.betaArch.formula.normalizedCoeff n =
        C.betaArch.betaArch.scalarRecord.scalar *
          (C.betaArch.betaArch.unfolding.mockCoeff n *
            C.betaArch.betaArch.unfolding.thetaCoeff n)) /\\
      (forall n, C.betaArch.betaArch.formula.normalizedCoeff n =
        C.betaArch.betaArch.formula.rademacher.main n +
          C.betaArch.betaArch.formula.rademacher.remainder n) :=
  A.paper_data_formula_proof_fields
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced restore the exact-coefficient audit accessor proposition")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """    let φ := ZMod.castHom (by simpa [Pk] using pow_dvd_pow p hkk)
      (ZMod (Pk p k'))
    change (M : ZMod (Pk p k')) * φ x.1 = 0
    calc
      (M : ZMod (Pk p k')) * φ x.1 =
          φ ((M : ZMod (Pk p k)) * x.1) := by
        rw [map_mul, map_natCast]
"""
    new = """    let φ : ZMod (Pk p k) →+* ZMod (Pk p k') :=
      ZMod.castHom (by simpa [Pk] using pow_dvd_pow p hkk)
        (ZMod (Pk p k'))
    change (M : ZMod (Pk p k')) * φ x.1 = 0
    calc
      (M : ZMod (Pk p k')) * φ x.1 =
          φ ((M : ZMod (Pk p k)) * x.1) := by
        simpa only [map_natCast] using
          (map_mul φ (M : ZMod (Pk p k)) x.1).symm
"""
    text, did = replace_once(text, old, new,
        "Mock2 type the prime-power reduction ring hom at both endpoints")
    changed |= did

    old = """        simp only [PkReduction, RingHom.toAddMonoidHom_apply, map_mul,
          map_natCast, map_intCast]
        rw [← mul_assoc, ← pow_add,
"""
    new = """        simp only [PkReduction, AddMonoidHom.coe_comp,
          Function.comp_apply, map_mul, map_natCast, map_intCast,
          Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
        rw [← mul_assoc, ← pow_add,
"""
    text, did = replace_once(text, old, new,
        "Mock2 unfold the right naturality reduction without a removed lemma")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """    DenseRange (coreToTrial M) := by
  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  simp [-SetLike.coe_sort_coe]
"""
    new = """    DenseRange (coreToTrial M) := by
  change DenseRange (Set.inclusion M.core.le_topologicalClosure)
  rw [denseRange_inclusion_iff]
  intro x hx
  exact hx
"""
    text, did = replace_once(text, old, new,
        "Mock2Advanced use the closure criterion for the core inclusion")
    changed |= did

    old = """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀]
  calc
"""
    new = """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀]
  have hstar :
      (starRingEnd ℂ) ((starRingEnd ℂ) (J.factor γ τ : ℂ)) =
        (J.factor γ τ : ℂ) := star_star _
  rw [hstar]
  calc
"""
    text, did = replace_once(text, old, new,
        "Mock2Advanced simplify the double conjugate underneath inversion")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")

    old = """theorem gammaTwoHyperbolic_mem :
    gammaTwoHyperbolic ∈ CongruenceSubgroup.Gamma 2 := by
  simp [gammaTwoHyperbolic, CongruenceSubgroup.Gamma_mem]
"""
    new = """theorem gammaTwoHyperbolic_mem :
    gammaTwoHyperbolic ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  norm_num [gammaTwoHyperbolic]
"""
    text, changed = replace_once(text, old, new,
        "FunctionalAnalysis verify the concrete Gamma(2) matrix entrywise")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
