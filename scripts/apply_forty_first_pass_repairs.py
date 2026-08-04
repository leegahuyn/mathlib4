from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 1:
        print(f"{label}: applied")
        return text.replace(old, new, 1), True
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    raise RuntimeError(f"{label}: expected one match, found {count}")


def replace_all(
    text: str, old: str, new: str, expected: int, label: str
) -> tuple[str, bool]:
    count = text.count(old)
    if count == expected:
        print(f"{label}: applied {count}")
        return text.replace(old, new), True
    if count == 0 and text.count(new) >= expected:
        print(f"{label}: already applied")
        return text, False
    raise RuntimeError(f"{label}: expected {expected} matches, found {count}")


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  residual_not_mem_theorem := by
    intro h
    cases h
""",
            """  residual_not_mem_theorem := by
    intro h
    have hEq :
        ("M 9.1.6 T/S residual table" : String) =
          "K.6 final statement Theorem K.2" := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
    exact (by decide : ("M 9.1.6 T/S residual table" : String) ≠
      "K.6 final statement Theorem K.2") hEq
""",
            "Mock1Advanced prove residual-table separation by literal inequality",
        ),
        (
            """    List.Mem C.instance C.registry.instances
""",
            """    List.Mem C.namedInstance C.registry.instances
""",
            "Mock1Advanced use namedInstance in checklist registry membership",
        ),
        (
            """    C.t1t5.t1.concrete = C.instance.concrete /\\
""",
            """    C.t1t5.t1.concrete = C.namedInstance.concrete /\\
""",
            "Mock1Advanced use namedInstance in checklist T1 link",
        ),
        (
            """theorem mem_all (c : RemainingAdvancedClaim) :
    List.Mem c all := by
  cases c <;> simp [all]
""",
            """theorem mem_all (c : RemainingAdvancedClaim) :
    List.Mem c all := by
  cases c with
  | abstractCertificate => exact List.Mem.head _
  | concreteCertificate => exact List.Mem.tail _ (List.Mem.head _)
  | claimRegistry => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | objectCoefficientSchema =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | paperObjectDataInstance =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
  | scalarJacobiDegeneracyRelation =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  | principalPartRationalSolve =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | completionShadowHolomorphic =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))
  | cuspTransport =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  | appellLerchBlockFormula =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  | principalExponentFormula =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.head _))))))))))
  | fixedShadowUnaryTheta =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  | insideOutsideQSeries =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.head _))))))))))))
""",
            "Mock1Advanced prove all remaining-claim memberships structurally",
        ),
        (
            """  m_mem := by
    simp [referenceMock1MList]
  formula_eq := by
""",
            """  m_mem := List.Mem.head _
  formula_eq := by
""",
            "Mock1Advanced prove the principal exponent index is the list head",
        ),
        (
            """theorem reference_paper_depth_one_matvec_eq_rhs :
    MatVecRat referencePaperDepthOneMatrix referencePaperDepthOneSolution =
      referencePaperDepthOneRHS := by
  decide
""",
            """theorem reference_paper_depth_one_matvec_eq_rhs :
    MatVecRat referencePaperDepthOneMatrix referencePaperDepthOneSolution =
      referencePaperDepthOneRHS := by
  norm_num [MatVecRat, dotRat, referencePaperDepthOneMatrix,
    referencePaperDepthOneSolution, referencePaperDepthOneRHS]
""",
            "Mock1Advanced normalize the depth-one rational matrix product",
        ),
        (
            """  rw [C.failureThickness_eq, C.thickness_eq]
  omega
""",
            """  rw [C.failureThickness_eq, C.thickness_eq]
""",
            "Mock1Advanced remove the tactic after thickness rewriting closes the goal",
        ),
        (
            """  infinity_mem := by
    simp [referenceRelevantCusps]
  zero_mem := by
    simp [referenceRelevantCusps]
  all_rows_preserved := by
    intro T hT
    simp at hT
    subst T
    rfl
""",
            """  infinity_mem := List.Mem.head _
  zero_mem := List.Mem.tail _ (List.Mem.head _)
  all_rows_preserved := by
    intro T hT
    have hEq : T = referenceTransportedPrincipalPart := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hT
    subst T
    rfl
""",
            "Mock1Advanced prove cusp and singleton transport membership structurally",
        ),
        (
            """theorem reference_cusp_convergence_passes :
    referenceCuspConvergenceProofDataCertificate.boundary.passes = true :=
  referenceCuspConvergenceProofDataCertificate.boundary_passes_at

theorem reference_transport_all_cusps_infinity :
""",
            """theorem reference_transport_all_cusps_infinity :
""",
            "Mock1Advanced remove the duplicate cusp-convergence theorem",
        ),
        (
            """end Mock1Advanced
end MockCert

namespace MockCert
namespace Mock1Advanced

/-!
""",
            """end Mock1Advanced
end MockCert

namespace MockCert
namespace Mock1Advanced

open Filter Topology

/-!
""",
            "Mock1Advanced reopen Filter and Topology in the resumed namespace",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    for name, label in [
        ("reference_depth_one_concrete_theorem_extraction",
         "Mock1Advanced mark the extracted depth-one theorem data noncomputable"),
        ("referenceRemainingClaimRegistryCertificate",
         "Mock1Advanced mark the remaining-claim registry noncomputable"),
        ("referenceCompletionShadowHolomorphicCertificate",
         "Mock1Advanced mark the completion-shadow wrapper noncomputable"),
        ("referenceCuspTransportClaimCertificate",
         "Mock1Advanced mark the cusp-transport wrapper noncomputable"),
        ("referenceTransportAcrossAllCuspsCertificate",
         "Mock1Advanced mark the all-cusps transport wrapper noncomputable"),
    ]:
        old = f"def {name} :"
        new = f"noncomputable def {name} :"
        text, did = replace_once(text, old, new, label)
        changed |= did

    text, did = replace_all(
        text, ".paperInstance.instance", ".paperInstance.namedInstance", 35,
        "Mock1Advanced update every renamed paper-instance projection")
    changed |= did

    old_section = """theorem mem_all (s : Section) :
    List.Mem s all := by
  cases s <;> simp [all]
"""
    new_section = """theorem mem_all (s : Section) :
    List.Mem s all := by
  cases s with
  | objectSchema => exact List.Mem.head _
  | t1t5 => exact List.Mem.tail _ (List.Mem.head _)
  | spt => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | kernel =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | exactCoefficient =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
  | pAdic =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  | entropyRepro =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | finalInstance =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))
"""
    text, did = replace_all(
        text, old_section, new_section, 2,
        "Mock1Advanced prove both section registries structurally")
    changed |= did

    group_sizes = [
        ("objectSchemaRequirements", 4),
        ("t1t5Requirements", 8),
        ("sptRequirements", 5),
        ("kernelRequirements", 8),
        ("exactCoefficientRequirements", 7),
        ("pAdicRequirements", 10),
        ("entropyReproRequirements", 9),
        ("finalInstanceRequirements", 3),
    ]
    for group, size in group_sizes:
        old = f"  cases r <;> simp [{group}, sectionOf] at h ⊢\n"
        alternatives = " | ".join(["rfl"] * size)
        new = (
            f"  simp only [{group}, List.mem_cons, List.not_mem_nil, or_false] at h\n"
            f"  rcases h with {alternatives} <;> rfl\n"
        )
        text, did = replace_all(
            text, old, new, 2,
            f"Mock1Advanced prove both {group} section maps from membership")
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """    simpa only [Int.cast_mul, Int.cast_pow,
      Int.cast_natCast] using hz
""",
            """    simpa only [Int.cast_mul, Int.cast_natCast,
      Nat.cast_pow] using hz
""",
            "Mock2 normalize the injectivity natural power cast",
        ),
        (
            """      simpa only [Int.cast_mul, Int.cast_pow,
        Int.cast_natCast] using hpz
""",
            """      simpa only [Int.cast_mul, Int.cast_natCast,
        Nat.cast_pow] using hpz
""",
            "Mock2 normalize the surjectivity natural power cast",
        ),
        (
            """    rw [powerShiftHom_intCast, hs, hq]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
""",
            """    rw [powerShiftHom_intCast, hs]
    have hqcast := congrArg
      (fun t : ℤ => (t : ZMod (Pk p k))) hq.symm
    simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow] using hqcast
""",
            "Mock2 cast the positive-valuation quotient representative equation",
        ),
        (
            """    rw [powerShiftHom_intCast]
    simp [hs]
""",
            """    rw [powerShiftHom_intCast]
    simp [shiftExponent, hm]
""",
            "Mock2 reduce the saturated power shift from its definition",
        ),
        (
            """  apply Nat.mul_right_cancel
  calc
""",
            """  apply Nat.mul_right_cancel (pow_pos hp.pos _)
  calc
""",
            "Mock2 provide positivity to natural right cancellation",
        ),
        (
            """  apply Subtype.ext
  simp [generic_quotientStep_eq_pow_shift M p k hM hp]
""",
            """  apply Subtype.ext
  change
    (p ^ shiftExponent M p k : ZMod (Pk p k)) *
        (z : ZMod (Pk p k)) =
      (Tor1Canonical.quotientStep M (Pk p k) : ZMod (Pk p k)) *
        (z : ZMod (Pk p k))
  rw [generic_quotientStep_eq_pow_shift M p k hM hp]
""",
            "Mock2 compare the two canonical kernel maps on underlying values",
        ),
        (
            """  ext x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have hz : (z : ZMod (p ^ thicknessExponent M p k)) =
      z • (1 : ZMod (p ^ thicknessExponent M p k)) := by
    simp
""",
            """  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have hz : (z : ZMod (p ^ thicknessExponent M p k)) =
      z • (1 : ZMod (p ^ thicknessExponent M p k)) := by
    exact (zsmul_one z).symm
""",
            "Mock2 keep the uniqueness calculation in the kernel subtype",
        ),
        (
            """@[simp] theorem PkReduction_intCast
    (p k k' : ℕ) (hkk : k' ≤ k) (z : ℤ) :
    PkReduction p k k' hkk (z : ZMod (Pk p k)) =
      (z : ZMod (Pk p k')) := by
  simp [PkReduction]
""",
            """@[simp] theorem PkReduction_intCast
    (p k k' : ℕ) (hkk : k' ≤ k) (z : ℤ) :
    PkReduction p k k' hkk (z : ZMod (Pk p k)) =
      (z : ZMod (Pk p k')) := by
  change
    ZMod.castHom (by simpa [Pk] using pow_dvd_pow p hkk)
        (ZMod (Pk p k')) (z : ZMod (Pk p k)) =
      (z : ZMod (Pk p k'))
  exact map_intCast
    (ZMod.castHom (by simpa [Pk] using pow_dvd_pow p hkk)
      (ZMod (Pk p k'))) z
""",
            "Mock2 prove prime-power reduction on integer representatives by map_intCast",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  rw [hu γ τ, hv γ τ, map_mul]
  rw [star_star]
""",
            """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀, star_star]
""",
            "Mock2Advanced move conjugation through the inverse before star-star",
        ),
        (
            """  simpa only [CuspQChart.transformedMeasure, pushFunction,
    Function.comp_apply, Equiv.symm_apply_apply] using
    (chart.coord.toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure
      (μ := μ) (g := pushFunction chart.coord.toEquiv u) (p := p))
""",
            """  change
    eLpNorm (pushFunction chart.coord.toEquiv u) p
        (Measure.map (⇑chart.coord.toMeasurableEquiv) μ) =
      eLpNorm u p μ
  simpa only [pushFunction, Function.comp_apply, Equiv.symm_apply_apply] using
    (chart.coord.toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure
      (μ := μ) (g := pushFunction chart.coord.toEquiv u) (p := p))
""",
            "Mock2Advanced expose the measurable-equivalence map in the Lp seminorm",
        ),
        (
            """  simpa only [CuspQChart.transformedMeasure, pushFunction,
    Function.comp_apply, Equiv.symm_apply_apply] using
    (chart.coord.toMeasurableEquiv.memLp_map_measure_iff
      (μ := μ) (g := pushFunction chart.coord.toEquiv u) (p := p))
""",
            """  change
    MemLp (pushFunction chart.coord.toEquiv u) p
        (Measure.map (⇑chart.coord.toMeasurableEquiv) μ) ↔
      MemLp u p μ
  simpa only [pushFunction, Function.comp_apply, Equiv.symm_apply_apply] using
    (chart.coord.toMeasurableEquiv.memLp_map_measure_iff
      (μ := μ) (g := pushFunction chart.coord.toEquiv u) (p := p))
""",
            "Mock2Advanced expose the measurable-equivalence map in MemLp",
        ),
        (
            """  simpa only [LinearMap.comp_apply] using hz
""",
            """  change (g z : A) = f z
  simpa only [LinearMap.comp_apply] using hz
""",
            "Mock2Advanced compare balanced equalizer lifts on subtype values",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    old = """    simpa [forward, backward, Function.comp_def] using hcomp.symm
"""
    new = """    change
      (Lp.compMeasurePreserving (⇑chart.coord.symm) hsymm)
          ((Lp.compMeasurePreserving (⇑chart.coord) hcoord) F) = F
    simpa [Function.comp_def] using hcomp.symm
"""
    text, did = replace_once(
        text, old, new,
        "Mock2Advanced expose the forward-backward Lp composition")
    changed |= did

    old = """    simpa [forward, backward, Function.comp_def] using hcomp.symm
"""
    new = """    change
      (Lp.compMeasurePreserving (⇑chart.coord) hcoord)
          ((Lp.compMeasurePreserving (⇑chart.coord.symm) hsymm) u) = u
    simpa [Function.comp_def] using hcomp.symm
"""
    text, did = replace_once(
        text, old, new,
        "Mock2Advanced expose the backward-forward Lp composition")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """              rw [hr, map_smulₛₗ]
              simp only [starRingEnd_apply, Complex.star_def,
                Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul] }
""",
            """              rw [hr, map_smulₛₗ]
              change
                (((starRingEnd ℂ) (r : ℂ)) * F v).re =
                  r * (F v).re
              rw [show (starRingEnd ℂ) (r : ℂ) = (r : ℂ) by
                simp [starRingEnd_apply, Complex.star_def]]
              exact Complex.re_ofReal_mul r (F v) }
""",
            "FunctionalAnalysis prove functional real-scalar compatibility directly",
        ),
        (
            """            rw [hr, map_smulₛₗ]
            simp only [starRingEnd_apply, Complex.star_def,
              Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul])
""",
            """            rw [hr, map_smulₛₗ]
            change
              (((starRingEnd ℂ) (r : ℂ)) * B u v).re =
                r * (B u v).re
            rw [show (starRingEnd ℂ) (r : ℂ) = (r : ℂ) by
              simp [starRingEnd_apply, Complex.star_def]]
            exact Complex.re_ofReal_mul r (B u v))
""",
            "FunctionalAnalysis prove form real-scalar compatibility directly",
        ),
        (
            """    simpa only [R, fredholmDefectKernelComplementRestriction_apply,
      ySeq, fredholmDefect_apply, sub_add_cancel, zero_add] using hSum
""",
            """    simpa only [Function.comp_apply, R,
      fredholmDefectKernelComplementRestriction_apply, ySeq,
      fredholmDefect_apply, sub_add_cancel, zero_add] using hSum
""",
            "FunctionalAnalysis unfold subsequence composition in the compact limit",
        ),
        (
            """    simpa only [S, R,
      fredholmDefectKernelComplementRestriction_apply] using
      hDefectTendsto.comp hψ.tendsto_atTop
""",
            """    change Filter.Tendsto
      ((fun n => S (x n : X)) ∘ ψ) Filter.atTop (nhds 0)
    simpa only [S, R,
      fredholmDefectKernelComplementRestriction_apply] using
      hDefectTendsto.comp hψ.tendsto_atTop
""",
            "FunctionalAnalysis state defect subsequence convergence as a composition",
        ),
        (
            """    simpa only [Function.comp_apply] using
      S.continuous.continuousAt.tendsto.comp hxTendsto
""",
            """    change Filter.Tendsto
      (S ∘ fun n => (x (ψ n) : X)) Filter.atTop (nhds (S y))
    exact S.continuous.continuousAt.tendsto.comp hxTendsto
""",
            "FunctionalAnalysis state continuity of the subsequence as a composition",
        ),
        (
            """  simpa only [LinearMap.mem_ker] using
    ((ContinuousLinearMap.adjoint A).ker.mem_orthogonal f)
""",
            """  change
    f ∈ (ContinuousLinearMap.adjoint A).kerᗮ ↔
      ∀ w : W, w ∈ (ContinuousLinearMap.adjoint A).ker → inner ℂ w f = 0
  exact (ContinuousLinearMap.adjoint A).ker.mem_orthogonal f
""",
            "FunctionalAnalysis state adjoint-kernel orthogonality by membership",
        ),
        (
            """    0 ≤ d.canonicalInverseNorm :=
  norm_nonneg _
""",
            """    0 ≤ d.canonicalInverseNorm := by
  change 0 ≤ ‖d.canonicalSolutionOperator‖
  exact norm_nonneg _
""",
            "FunctionalAnalysis expose the canonical inverse norm definition",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    old = """  have hzero : (u : V) - (v : V) = 0 := by
    apply inner_self_eq_zero.mp
    exact A.ker.inner_right_of_mem_orthogonal hker horth
"""
    new = """  have hzero : (u : V) - (v : V) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    exact A.ker.inner_right_of_mem_orthogonal hker horth
"""
    text, did = replace_once(
        text, old, new,
        "FunctionalAnalysis specify the scalar field in inner_self_eq_zero")
    changed |= did

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
