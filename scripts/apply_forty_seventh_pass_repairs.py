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
    ends = text.count(end)
    if starts != 1 or ends < 1:
        if replacement in text:
            print(f"{label}: already applied")
            return text, False
        raise RuntimeError(
            f"{label}: expected one start and at least one end, found {starts}/{ends}"
        )
    i = text.index(start)
    j = text.index(end, i)
    print(f"{label}: applied")
    return text[:i] + replacement + text[j:], True


def nested_mem_proof(index: int) -> str:
    proof = "List.Mem.head _"
    for _ in range(index):
        proof = f"List.Mem.tail _ ({proof})"
    return proof


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")

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

    lines: list[str] = []
    lines += [
        "private theorem mem_all_aux (r : AdvancedClaimsIIRequirement) :",
        "    List.Mem r all := by",
        "  cases r with",
    ]
    for index, ctor in enumerate(constructors):
        lines += [f"  | {ctor} =>", f"      exact {nested_mem_proof(index)}"]
    lines.append("")

    for group, section in groups:
        lines += [
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

    for group, _ in groups:
        lines += [
            f"theorem {group}_mem_all",
            "    (r : AdvancedClaimsIIRequirement)",
            f"    (_h : List.Mem r {group}Requirements) :",
            "    List.Mem r all :=",
            "  mem_all_aux r",
            "",
        ]

    lines += [
        "theorem mem_all (r : AdvancedClaimsIIRequirement) :",
        "    List.Mem r all :=",
        "  mem_all_aux r",
        "",
    ]
    replacement = "\n".join(lines)

    text, changed = replace_between(
        text,
        "theorem sectionOf_objectSchema_at\n",
        "end AdvancedClaimsIIRequirement\n",
        replacement,
        "Mock1Advanced centralize the advanced-claims registry membership proof",
    )
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
        text, old, new,
        "Mock2 calculate the reduced kernel membership through the ring hom")
    changed |= did

    old = """  rw [powerShiftHom_intCast, rightThicknessMap_intCast_as_intCast,
    powerShiftHom_intCast]
  simp [PkReduction, ← mul_assoc, ← Nat.cast_mul, ← pow_add,
    Nat.add_sub_of_le (shiftExponent_mono_of_le_k M p hkk)]
"""
    new = """  rw [powerShiftHom_intCast, rightThicknessMap_intCast]
  simp only [PkReduction, RingHom.toAddMonoidHom_apply, map_mul,
    map_natCast]
  rw [← mul_assoc, ← pow_add,
    Nat.add_sub_of_le (shiftExponent_mono_of_le_k M p hkk)]
"""
    text, did = replace_once(
        text, old, new,
        "Mock2 compute the right naturality square before integer recasting")
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
    text, did = replace_once(
        text, old, new,
        "Mock2Advanced use the canonical dense-range inclusion criterion")
    changed |= did

    old = """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀]
  simp only [star_star]
  calc
"""
    new = """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀]
  calc
"""
    text, did = replace_once(
        text, old, new,
        "Mock2Advanced remove the no-progress star simplification")
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
        text, old, new,
        "FunctionalAnalysis expose the defect restriction before cancellation")
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
