from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        raise RuntimeError(f"{label}: source changed; expected block not found")
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def replace_between(
    text: str, start: str, end: str, replacement: str, label: str
) -> tuple[str, bool]:
    starts = text.count(start)
    if starts != 1:
        if replacement in text:
            print(f"{label}: already applied")
            return text, False
        raise RuntimeError(f"{label}: expected one start, found {starts}")
    i = text.index(start)
    try:
        j = text.index(end, i)
    except ValueError as exc:
        if replacement in text:
            print(f"{label}: already applied")
            return text, False
        raise RuntimeError(f"{label}: end marker not found") from exc
    print(f"{label}: applied")
    return text[:i] + replacement + text[j:], True


def nested_mem_proof(index: int) -> str:
    proof = "List.Mem.head _"
    for _ in range(index):
        proof = f"List.Mem.tail _ ({proof})"
    return proof


def theorem_result(
    text: str, namespace: str, theorem: str, before: int
) -> str:
    ns_start = text.rfind(f"namespace {namespace}", 0, before)
    if ns_start < 0:
        raise RuntimeError(f"namespace {namespace} not found before audit structure")
    theorem_start = text.index(f"theorem {theorem}\n", ns_start, before)
    assign = text.index(" :=\n", theorem_start, before)
    header = text[theorem_start:assign]
    separator = header.rfind(" :\n")
    if separator < 0:
        raise RuntimeError(f"result separator for {namespace}.{theorem} not found")
    result = header[separator + 3 :]
    return " ".join(line.strip() for line in result.splitlines())


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    constructors = [
        "objectClaimRegistry",
        "objectCoefficientSchema",
        "paperObjectDataInstance",
        "scalarJacobiDegeneracyRelation",
        "principalPartRationalSolve",
        "completionShadowHolomorphicConsequence",
        "cuspTransportSkeleton",
        "appellLerchBlockFormula",
        "principalExponentFormula",
        "paperMatrixRhsSolution",
        "fixedShadowUnaryThetaData",
        "insideOutsideQSeriesCertificate",
        "natGcdLcmSkeleton",
        "primewiseThicknessSkeleton",
        "actualMpkValuationCertificate",
        "obstructionFreeFailureThicknessPortfolio",
        "baseChangeStabilityBoundary",
        "kernelSelectionCertificateBoundary",
        "finiteMultiplierPhaseMatchingCertificate",
        "cuspConvergenceCertificateBoundary",
        "transportFamilyConnection",
        "kernelSelectionTableInput",
        "multiplierPhaseMatchingInput",
        "cuspConvergenceProofData",
        "transportAcrossRelevantCusps",
        "coefficientSeparationBoundary",
        "thetaCoefficientCharacterBoundary",
        "spectralKloostermanExpansionBoundary",
        "localEulerDecompositionBoundary",
        "rootNumberFilterBoundary",
        "exactCoefficientFormulaBoundary",
        "paperDataFormulaProofFields",
        "padicNormalizationWrapper",
        "padicOverlapGluingWrapper",
        "mahlerInterpolationWrapper",
        "analyticRangeTailZeroWrapper",
        "globalPadicFaceTracking",
        "denominatorClearingData",
        "chartVectorsModuloPrimePower",
        "mahlerTableInterpolationVector",
        "analyticRangePredicate",
        "obstructionFailureCaseInstance",
        "regressionCardySkeleton",
        "rademacherTailSkeleton",
        "entropyCardyPaperWrapper",
        "actualEntropyAlphaExtraction",
        "degeneracyChannelInstance",
        "rationalOlsIntervalTable",
        "growthStabilityUnderSptPadic",
        "reproducibilitySchemaValidator",
        "externalOutputSchemaRows",
        "namedConcretePaperInstance",
        "concreteCertificateTheoremExtraction",
        "advancedClaimsGlobalChecklist",
    ]
    groups = [
        ("objectSchema", "Section.objectSchema"),
        ("t1t5", "Section.t1t5"),
        ("spt", "Section.spt"),
        ("kernel", "Section.kernel"),
        ("exactCoefficient", "Section.exactCoefficient"),
        ("pAdic", "Section.pAdic"),
        ("entropyRepro", "Section.entropyRepro"),
        ("finalInstance", "Section.finalInstance"),
    ]

    lines: list[str] = [
        "private theorem mem_all_aux (r : AdvancedClaimsIIRequirement) :",
        "    List.Mem r all := by",
        "  cases r with",
    ]
    for index, constructor in enumerate(constructors):
        lines.extend(
            [f"  | {constructor} =>", f"      exact {nested_mem_proof(index)}"]
        )
    lines.append("")

    for group, section in groups:
        lines.extend(
            [
                f"theorem sectionOf_{group}_at",
                "    (r : AdvancedClaimsIIRequirement)",
                f"    (h : List.Mem r {group}Requirements) :",
                f"    sectionOf r = {section} := by",
                "  have hm :",
                f"      List.Mem (sectionOf r) ({group}Requirements.map sectionOf) :=",
                "    List.mem_map_of_mem h",
                f"  simpa [{group}Requirements, sectionOf] using hm",
                "",
            ]
        )

    for group, _section in groups:
        lines.extend(
            [
                f"theorem {group}_mem_all",
                "    (r : AdvancedClaimsIIRequirement)",
                f"    (_h : List.Mem r {group}Requirements) :",
                "    List.Mem r all :=",
                "  mem_all_aux r",
                "",
            ]
        )

    lines.extend(
        [
            "theorem mem_all (r : AdvancedClaimsIIRequirement) :",
            "    List.Mem r all :=",
            "  mem_all_aux r",
            "",
        ]
    )
    registry_replacement = "\n".join(lines)
    text, did = replace_between(
        text,
        "theorem sectionOf_objectSchema_at\n",
        "end AdvancedClaimsIIRequirement\n",
        registry_replacement,
        "Mock1Advanced centralize the advanced-claims registry membership proof",
    )
    changed |= did

    audit_start = text.index("structure AdvancedClaimsIIActualInputAuditCertificate")
    field_specs = [
        ("paper_object_data_instance", "PaperDataInstancePayloadCertificate", "paper_object_instance_at", ""),
        ("scalar_jacobi_degeneracy", "PaperDataInstancePayloadCertificate", "scalar_jacobi_at", "forall n, "),
        ("appell_lerch_block_formula", "PaperDataInstancePayloadCertificate", "appell_lerch_at", ""),
        ("principal_exponent_formula", "PaperDataInstancePayloadCertificate", "principal_exponent_at", ""),
        ("paper_matrix_rhs_solution", "PaperDataInstancePayloadCertificate", "matrix_solution_at", ""),
        ("fixed_shadow_unary_theta_data", "PaperDataInstancePayloadCertificate", "fixed_shadow_at", ""),
        ("inside_outside_qseries", "PaperDataInstancePayloadCertificate", "inside_outside_at", "forall n, "),
        ("actual_mpk_valuation_certificate", "SPTKernelRequirementPayloadCertificate", "valuation_certificate_at", ""),
        ("kernel_selection_table_input", "SPTKernelRequirementPayloadCertificate", "kernel_table_at", ""),
        ("multiplier_phase_matching_input", "SPTKernelRequirementPayloadCertificate", "multiplier_input_at", ""),
        ("cusp_convergence_proof_data", "SPTKernelRequirementPayloadCertificate", "cusp_input_at", ""),
        ("paper_data_formula_proof_fields", "ExactCoefficientRequirementPayloadCertificate", "paper_formula_fields_at", ""),
        ("denominator_clearing_data", "PAdicRequirementPayloadCertificate", "denominator_data_at", ""),
        ("chart_vectors_modulo_prime_power", "PAdicRequirementPayloadCertificate", "chart_vectors_at", "forall n, "),
        ("mahler_table_interpolation_vector", "PAdicRequirementPayloadCertificate", "mahler_table_at", "forall n, "),
        (
            "analytic_range_predicate",
            "PAdicRequirementPayloadCertificate",
            "predicate_at",
            "forall n, (hn : C.padicAnalyticRange.cutoff <= n) -> ",
        ),
        ("obstruction_failure_case_instance", "PAdicRequirementPayloadCertificate", "obstruction_failure_at", ""),
        ("actual_entropy_alpha_extraction", "EntropyReproRequirementPayloadCertificate", "alpha_extraction_at", ""),
        ("degeneracy_channel_instance", "EntropyReproRequirementPayloadCertificate", "degeneracy_at", "forall n, "),
        ("rational_ols_interval_table", "EntropyReproRequirementPayloadCertificate", "ols_interval_at", ""),
        ("external_output_schema_rows", "EntropyReproRequirementPayloadCertificate", "external_rows_at", ""),
    ]
    field_lines: list[str] = []
    for field, namespace, theorem, binder in field_specs:
        result = theorem_result(text, namespace, theorem, audit_start)
        field_lines.extend([f"  {field} :", f"    {binder}({result})"])
    audit_replacement = "\n".join(field_lines)
    text, did = replace_between(
        text,
        "  paper_object_data_instance :\n",
        "\n\nnamespace AdvancedClaimsIIActualInputAuditCertificate\n",
        audit_replacement,
        "Mock1Advanced restore audit fields to the propositions proved by their payload lemmas",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  toFun x := ⟨PkReduction p k k' hkk x.1, by
    apply (Tor1CyclicModel_mem_iff M (Pk p k') _).2
    let φ := ZMod.castHom (by simpa [Pk] using pow_dvd_pow p hkk)
      (ZMod (Pk p k'))
    have hx := congrArg φ x.2
    change φ ((M : ZMod (Pk p k)) * x.1) = φ 0 at hx
    simpa only [map_mul, map_natCast, map_zero] using hx⟩
"""
    new = """  toFun x := ⟨PkReduction p k k' hkk x.1, by
    apply (Tor1CyclicModel_mem_iff M (Pk p k') _).2
    let φ := ZMod.castHom (by simpa [Pk] using pow_dvd_pow p hkk)
      (ZMod (Pk p k'))
    change (M : ZMod (Pk p k')) * φ x.1 = 0
    calc
      (M : ZMod (Pk p k')) * φ x.1 =
          φ ((M : ZMod (Pk p k)) * x.1) := by
        rw [map_mul, map_natCast]
      _ = φ 0 := congrArg φ x.2
      _ = 0 := map_zero φ⟩
"""
    text, did = replace_once(
        text,
        old,
        new,
        "Mock2 calculate the reduced kernel membership through the ring hom",
    )
    changed |= did

    old = """  rw [powerShiftHom_intCast, rightThicknessMap_intCast_as_intCast,
    powerShiftHom_intCast]
  simp [PkReduction, ← mul_assoc, ← Nat.cast_mul, ← pow_add,
    Nat.add_sub_of_le (shiftExponent_mono_of_le_k M p hkk)]
"""
    new = """  calc
    PkReduction p k k' hkk
        (powerShiftHom M p k
          (z : ZMod (p ^ thicknessExponent M p k))) =
      PkReduction p k k' hkk
        ((p ^ shiftExponent M p k : ZMod (Pk p k)) *
          (z : ZMod (Pk p k))) :=
        congrArg (PkReduction p k k' hkk)
          (powerShiftHom_intCast M p k z)
    _ =
      (p ^ shiftExponent M p k' : ZMod (Pk p k')) *
        ((((p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z : ℤ) :
          ZMod (Pk p k')) := by
        simp only [PkReduction, RingHom.toAddMonoidHom_apply, map_mul,
          map_natCast, map_intCast]
        rw [← mul_assoc, ← pow_add,
          Nat.add_sub_of_le (shiftExponent_mono_of_le_k M p hkk)]
    _ = powerShiftHom M p k'
        (((((p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z : ℤ)) :
          ZMod (p ^ thicknessExponent M p k')) :=
      (powerShiftHom_intCast M p k'
        (((p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z)).symm
    _ = powerShiftHom M p k'
        (rightThicknessMap M p hkk
          (z : ZMod (p ^ thicknessExponent M p k))) := by
      rw [rightThicknessMap_intCast_as_intCast]
"""
    text, did = replace_once(
        text,
        old,
        new,
        "Mock2 calculate right naturality through explicit representative formulas",
    )
    changed |= did

    old = """      agrees_with_gcd_on_representatives :=
        Tor1PrimePowerCanonical.
          powerShiftKernelHom_agrees_gcdToKernelHom_intCast M p k hM hp
"""
    new = """      agrees_with_gcd_on_representatives :=
        Tor1PrimePowerCanonical.powerShiftKernelHom_agrees_gcdToKernelHom_intCast
          M p k hM hp
"""
    text, did = replace_once(
        text,
        old,
        new,
        "Mock2 remove invalid field notation across the namespace line break",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀]
  simp only [star_star]
  calc
"""
    new = """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀]
  calc
"""
    text, did = replace_once(
        text,
        old,
        new,
        "Mock2Advanced remove the no-progress star simplification",
    )
    changed |= did

    old = """    simpa [Function.comp_def] using hcomp.symm
"""
    new = """    simpa only [Function.comp_def,
      Lp.compMeasurePreserving_id_apply] using hcomp.symm
"""
    count = text.count(old)
    if count == 2:
        text = text.replace(old, new)
        changed = True
        print("Mock2Advanced reduce both identity Lp pullbacks: applied 2")
    elif count == 0 and text.count(new) >= 2:
        print("Mock2Advanced identity Lp pullbacks: already applied")
    else:
        raise RuntimeError(
            f"Mock2Advanced identity Lp pullbacks: expected two old blocks, found {count}"
        )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")

    old = """    have hfun :
        (fun n => R (x (ψ n)) + ySeq (ψ n)) =
          (fun n => (x (ψ n) : X)) := by
      funext n
      simp only [R, ySeq,
        fredholmDefectKernelComplementRestriction_apply,
        fredholmDefect_apply, sub_add_cancel]
"""
    new = """    have hfun :
        (fun n => R (x (ψ n)) + ySeq (ψ n)) =
          (fun n => (x (ψ n) : X)) := by
      funext n
      change
        ((x (ψ n) : X) - K (x (ψ n) : X)) +
            K (x (ψ n) : X) = (x (ψ n) : X)
      exact sub_add_cancel _ _
"""
    text, changed = replace_once(
        text,
        old,
        new,
        "FunctionalAnalysis expose the defect restriction before cancellation",
    )
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
