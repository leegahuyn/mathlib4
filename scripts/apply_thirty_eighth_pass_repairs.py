from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  residual_not_mem_theorem := by
    decide
""",
            """  residual_not_mem_theorem := by
    intro h
    cases h
""",
            "Mock1Advanced eliminate impossible residual-table membership structurally",
        ),
        (
            """def referenceMock1DepthOneQSeriesCertificate :
    ObjectQSeriesCertificate where
""",
            """noncomputable def referenceMock1DepthOneQSeriesCertificate :
    ObjectQSeriesCertificate where
""",
            "Mock1Advanced mark the depth-one q-series certificate noncomputable",
        ),
        (
            """    qSeriesCertificate := referenceMock1DepthOneQSeriesCertificate
    qSeriesCertificate_matches := rfl
    entropyProof := by
""",
            """    qSeriesCertificate := referenceMock1DepthOneQSeriesCertificate
    qSeriesCertificate_matches := rfl
    alpha := 1
    beta := 0
    entropyProof := by
""",
            "Mock1Advanced update depth-one entropy parameters together with the object",
        ),
        (
            """  shadow_zero_after_completion := by
    intro h x
    simp [referenceMock1DepthOneConcreteCertificate, referenceShadow]
""",
            """  shadow_zero_after_completion := by
    intro _ x
    change (0 : Complex) = 0
    rfl
""",
            "Mock1Advanced compute the depth-one shadow directly",
        ),
        (
            """abbrev referencePaperInstancesHRflConcrete : ConcreteCertificate Unit :=
""",
            """noncomputable abbrev referencePaperInstancesHRflConcrete : ConcreteCertificate Unit :=
""",
            "Mock1Advanced mark the extracted RFL concrete certificate noncomputable",
        ),
        (
            """theorem mem_all (a : PaperInstancesHRlfAxis) :
    List.Mem a all := by
  cases a <;> decide
""",
            """theorem mem_all (a : PaperInstancesHRlfAxis) :
    List.Mem a all := by
  cases a with
  | rademacher => exact List.Mem.head _
  | lerchPrincipal => exact List.Mem.tail _ (List.Mem.head _)
  | fourier => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
""",
            "Mock1Advanced prove the three RLF axes structurally",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    anchor = """structure PaperInstancesHRlfMathematicalPayloadCertificate : Prop where
"""
    aliases = """def PaperInstancesHRlfCoefficientDetailedProp (n : Nat) : Prop :=
  referencePaperInstancesHRflConcrete.qSeriesCertificate.series.coeff n =
      referencePaperInstancesHRflConcrete.object.coeff n /\\
    referencePaperInstancesHRflConcrete.qSeriesCertificate.series.coefficientAt n =
        referencePaperInstancesHRflConcrete.object.coeff n /\\
      referencePaperInstancesHCompletionCertificate.t1t5.exactCoefficient.formula.coefficient n =
        referencePaperInstancesHCompletionCertificate.t1t5.exactCoefficient.spectral.rademacher.main n +
          referencePaperInstancesHCompletionCertificate.t1t5.exactCoefficient.spectral.rademacher.remainder n

def PaperInstancesHRlfPadicDetailedProp (n : Nat) : Prop :=
  IntCongruent referencePaperInstancesHRflConcrete.padicOverlap.M
      (referencePaperInstancesHRflConcrete.padicOverlap.left n)
      (referencePaperInstancesHRflConcrete.padicOverlap.right n) /\\
    IntCongruent
        (PrimePower referencePaperInstancesHRflConcrete.padicOverlap.p
          referencePaperInstancesHRflConcrete.padicOverlap.k)
        (referencePaperInstancesHRflConcrete.padicOverlap.left n)
        (referencePaperInstancesHRflConcrete.padicOverlap.right n) /\\
      IntCongruent
          (PrimePower referencePaperInstancesHRflConcrete.mahler.p
            referencePaperInstancesHRflConcrete.mahler.k)
          (referencePaperInstancesHRflConcrete.mahler.eval n)
          (referencePaperInstancesHRflConcrete.mahler.target n) /\\
        referencePaperInstancesHRflConcrete.mahler.eval n =
            Finset.sum Finset.univ
              (fun j : Fin referencePaperInstancesHRflConcrete.mahler.length =>
                referencePaperInstancesHRflConcrete.mahler.coeff j *
                  referencePaperInstancesHRflConcrete.mahler.basis j n) /\\
          FiniteCongruenceMod referencePaperInstancesHRflConcrete.mahlerBinomial.p
              referencePaperInstancesHRflConcrete.mahlerBinomial.k
              (referencePaperInstancesHRflConcrete.mahlerBinomial.eval n)
              (referencePaperInstancesHRflConcrete.mahlerBinomial.target n) /\\
            referencePaperInstancesHRflConcrete.mahlerBinomial.eval n =
              Finset.sum Finset.univ
                (fun j : Fin referencePaperInstancesHRflConcrete.mahlerBinomial.length =>
                  referencePaperInstancesHRflConcrete.mahlerBinomial.coeff j *
                    mahlerBinomialBasis (j : Nat) n)

def PaperInstancesHRlfEntropyDetailedProp : Prop :=
  Tendsto
      (fun n =>
        Real.log |referencePaperInstancesHRflConcrete.object.coeff n| -
          referencePaperInstancesHRflConcrete.alpha * Real.sqrt (n : Real) +
            (1 / 2 : Real) * Real.log (n : Real))
      atTop (nhds referencePaperInstancesHRflConcrete.beta) /\\
    referencePaperInstancesHCompletionCertificate.analytic.entropyCardy.alphaExtraction.alphaInterval.Contains
        referencePaperInstancesHCompletionCertificate.analytic.entropyCardy.alphaExtraction.alphaHat /\\
      referencePaperInstancesHCompletionCertificate.analytic.entropyCardy.cardyConvention.ceffInterval.Contains
        referencePaperInstancesHCompletionCertificate.analytic.entropyCardy.cardyConvention.ceffHat

""" + anchor
    text, did = replace_once(
        text, anchor, aliases,
        "Mock1Advanced define explicit propositions for the RLF payload links")
    changed |= did

    old = """  coefficient_matches_detailed :
    forall n,
      rfl_detailed.coefficient_extraction n /\\
        rfl_detailed.coefficient_at_extraction n /\\
          rfl_detailed.exact_rademacher_decomposition n
  padic_matches_detailed :
    forall n,
      rfl_detailed.padic_overlap_mod_m n /\\
        rfl_detailed.padic_overlap_prime_power n /\\
          rfl_detailed.mahler_congruence n /\\
            rfl_detailed.mahler_expansion n /\\
              rfl_detailed.mahler_binomial_congruence n /\\
                rfl_detailed.mahler_binomial_expansion n
  entropy_matches_detailed :
    rfl_detailed.entropy_limit_formula /\\
      rfl_detailed.cardy_alpha_mem /\\
        rfl_detailed.cardy_ceff_mem
"""
    new = """  coefficient_matches_detailed :
    forall n, PaperInstancesHRlfCoefficientDetailedProp n
  padic_matches_detailed :
    forall n, PaperInstancesHRlfPadicDetailedProp n
  entropy_matches_detailed :
    PaperInstancesHRlfEntropyDetailedProp
"""
    text, did = replace_once(
        text, old, new,
        "Mock1Advanced use propositions rather than proof terms in payload fields")
    changed |= did

    old = """theorem coefficient_matches_detailed_at
    (C : PaperInstancesHRlfMathematicalPayloadCertificate) (n : Nat) :
    C.rfl_detailed.coefficient_extraction n /\\
      C.rfl_detailed.coefficient_at_extraction n /\\
        C.rfl_detailed.exact_rademacher_decomposition n :=
  C.coefficient_matches_detailed n

theorem padic_matches_detailed_at
    (C : PaperInstancesHRlfMathematicalPayloadCertificate) (n : Nat) :
    C.rfl_detailed.padic_overlap_mod_m n /\\
      C.rfl_detailed.padic_overlap_prime_power n /\\
        C.rfl_detailed.mahler_congruence n /\\
          C.rfl_detailed.mahler_expansion n /\\
            C.rfl_detailed.mahler_binomial_congruence n /\\
              C.rfl_detailed.mahler_binomial_expansion n :=
  C.padic_matches_detailed n

theorem entropy_matches_detailed_at
    (C : PaperInstancesHRlfMathematicalPayloadCertificate) :
    C.rfl_detailed.entropy_limit_formula /\\
      C.rfl_detailed.cardy_alpha_mem /\\
        C.rfl_detailed.cardy_ceff_mem :=
  C.entropy_matches_detailed
"""
    new = """theorem coefficient_matches_detailed_at
    (C : PaperInstancesHRlfMathematicalPayloadCertificate) (n : Nat) :
    PaperInstancesHRlfCoefficientDetailedProp n :=
  C.coefficient_matches_detailed n

theorem padic_matches_detailed_at
    (C : PaperInstancesHRlfMathematicalPayloadCertificate) (n : Nat) :
    PaperInstancesHRlfPadicDetailedProp n :=
  C.padic_matches_detailed n

theorem entropy_matches_detailed_at
    (C : PaperInstancesHRlfMathematicalPayloadCertificate) :
    PaperInstancesHRlfEntropyDetailedProp :=
  C.entropy_matches_detailed
"""
    text, did = replace_once(
        text, old, new,
        "Mock1Advanced update RLF payload accessors to the explicit propositions")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  refine ⟨2, 1, 1, by norm_num, ?_⟩
  norm_num
""",
            """  refine ⟨2, 1, 1, by norm_num, ?_⟩
  norm_num [starRingEnd_apply, Complex.star_def]
""",
            "Mock2Advanced evaluate conjugation in the scalar counterexample",
        ),
        (
            """  rw [hu γ τ, hv γ τ]
  simp only [map_mul, star_star]
""",
            """  rw [hu γ τ, hv γ τ, map_mul]
  rw [star_star]
""",
            "Mock2Advanced simplify the conjugate-dual multiplier explicitly",
        ),
        (
            """  map_eq := by
    simpa only [CuspQChart.transformedMeasure] using
      (MeasurableEquiv.map_symm_map
        (μ := μ) chart.coord.toMeasurableEquiv)
""",
            """  map_eq := by
    change Measure.map (⇑chart.coord.toMeasurableEquiv.symm)
      (Measure.map (⇑chart.coord.toMeasurableEquiv) μ) = μ
    exact MeasurableEquiv.map_symm_map
      (μ := μ) chart.coord.toMeasurableEquiv
""",
            "Mock2Advanced expose the measurable equivalence in map_symm_map",
        ),
        (
            """  add_mem' := by
    intro σ τ hσ hτ r s
    rw [map_add, hσ r s, hτ r s]
  smul_mem' := by
    intro c σ hσ r s
    rw [map_smul, hσ r s]
""",
            """  add_mem' := by
    intro σ τ hσ hτ r s
    change L.transport r s (σ r + τ r) = σ s + τ s
    rw [map_add, hσ r s, hτ r s]
  smul_mem' := by
    intro c σ hσ r s
    change L.transport r s (c • σ r) = c • σ s
    rw [map_smul, hσ r s]
""",
            "Mock2Advanced expose pointwise operations in flat sections",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    count = text.count("(p : ℝ≥0∞)")
    if count:
        text = text.replace("(p : ℝ≥0∞)", "(p : ENNReal)")
        changed = True
        print(f"Mock2Advanced replace unsupported ENNReal binder notation: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """              simpa only [starRingEnd_apply, Complex.star_def,
                Complex.conj_ofReal, smul_eq_mul, Complex.mul_re,
                Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] }
""",
            """              change r * (F v).re - 0 * (F v).im = r * (F v).re
              ring }
""",
            "FunctionalAnalysis calculate real scalar anti-linearity by components",
        ),
        (
            """            simpa only [starRingEnd_apply, Complex.star_def,
              Complex.conj_ofReal, smul_eq_mul, Complex.mul_re,
              Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero])
""",
            """            change r * (B u v).re - 0 * (B u v).im = r * (B u v).re
            ring)
""",
            "FunctionalAnalysis calculate form anti-linearity by components",
        ),
        (
            """      have hstar : starRingEnd ℂ Complex.I = -Complex.I := by
        simpa only [starRingEnd_apply, Complex.star_def] using Complex.conj_I
""",
            """      have hstar : starRingEnd ℂ Complex.I = -Complex.I := by
        exact Complex.conj_I
""",
            "FunctionalAnalysis use the direct conjugation theorem for I",
        ),
        (
            """  apply isCompactOperator_of_tendsto
  · exact tendsto_iff_norm_sub_tendsto_zero.mpr h.tail_norm
  · exact Filter.Eventually.of_forall h.truncation_isCompact
""",
            """  exact isCompactOperator_of_tendsto (l := Filter.atTop)
    (tendsto_iff_norm_sub_tendsto_zero.mpr h.tail_norm)
    (Filter.Eventually.of_forall h.truncation_isCompact)
""",
            "FunctionalAnalysis specify the compact-limit filter",
        ),
        (
            """theorem solve_spec
    (d : FredholmBypassData A) (F : W) :
    A (d.solve F) = F := by
  change d.unshiftedEquiv (d.unshiftedEquiv.symm F) = F
  exact d.unshiftedEquiv.apply_symm_apply F
""",
            """theorem solve_spec
    (d : FredholmBypassData A) (F : W) :
    A (d.solve F) = F := by
  rw [← d.unshiftedEquiv_apply (d.solve F)]
  simpa only [solve, solutionOperator] using
    d.unshiftedEquiv.apply_symm_apply F
""",
            "FunctionalAnalysis connect solve to the unshifted equivalence",
        ),
        (
            """  have hZero : (u : X) - (v : X) = 0 := by
    apply inner_self_eq_zero.mp
    exact (fredholmDefect K).ker.inner_right_of_mem_orthogonal hKer hOrth
""",
            """  have hZero : (u : X) - (v : X) = 0 := by
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp
      ((fredholmDefect K).ker.inner_right_of_mem_orthogonal hKer hOrth)
""",
            "FunctionalAnalysis specify the scalar field in inner_self_eq_zero",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
