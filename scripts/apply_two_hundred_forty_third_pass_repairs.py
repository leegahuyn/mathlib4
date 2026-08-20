from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """    rw [(contDiffWithinAt_localInvariantProp
      (I := 𝓘(ℂ))
      (I' := 𝓘(ℂ, OneFormValue I_G G)) ∞).liftPropAt_iff_comp_inclusion
        (coverOpen_mono (C.piece_le_target i))]
    exact hlocal tau_i
""",
        """    change ChartedSpace.LiftPropAt
      (ContDiffWithinAtProp
        𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞)
      (strictGluedToFun I_G G C s)
      (Set.inclusion (coverOpen_mono (C.piece_le_target i)) tau_i)
    rw [(contDiffWithinAt_localInvariantProp
      (I := 𝓘(ℂ))
      (I' := 𝓘(ℂ, OneFormValue I_G G)) ∞).liftPropAt_iff_comp_inclusion
        (coverOpen_mono (C.piece_le_target i))]
    exact hlocal tau_i
""",
        "Mock2 expose the open inclusion before local smoothness transport",
    )
    m2 = replace_exact(
        m2,
        """  rw [show deckPullback I_G G γ U (A + C) =
      deckPullback I_G G γ U A + deckPullback I_G G γ U C by
    exact deckPullback_add I_G G γ U A C]
  rw [hA γ τ, hC γ τ]
  exact (smul_add _ _ _).symm
""",
        """  rw [show deckPullback I_G G γ U (A + C) =
      deckPullback I_G G γ U A + deckPullback I_G G γ U C by
    exact deckPullback_add I_G G γ U A C]
  change
    deckPullback I_G G γ U A τ + deckPullback I_G G γ U C τ =
      (M.automorphyFactor γ (τ : H) : ℂ) • (A τ + C τ)
  rw [hA γ τ, hC γ τ]
  exact (smul_add _ _ _).symm
""",
        "Mock2 expose pointwise addition in equation 6.2",
    )
    m2 = replace_exact(
        m2,
        """  rw [show deckPullback I_G G γ U (-A) =
      -deckPullback I_G G γ U A by
    exact deckPullback_neg I_G G γ U A]
  rw [hA γ τ]
  exact (smul_neg _ _).symm
""",
        """  rw [show deckPullback I_G G γ U (-A) =
      -deckPullback I_G G γ U A by
    exact deckPullback_neg I_G G γ U A]
  change
    -deckPullback I_G G γ U A τ =
      (M.automorphyFactor γ (τ : H) : ℂ) • (-A τ)
  rw [hA γ τ]
  exact (smul_neg _ _).symm
""",
        "Mock2 expose pointwise negation in equation 6.2",
    )
    m2 = replace_exact(
        m2,
        """theorem ext_pointwise {U : Opens} {g h : SmoothGaugeMap I_G G U}
    (hfun : ∀ τ, g τ = h τ) : g = h :=
  ext (funext hfun)
""",
        """theorem ext_pointwise {U : Opens} {g h : SmoothGaugeMap I_G G U}
    (hfun : ∀ τ, g τ = h τ) : g = h :=
  SmoothGaugeMap.ext (funext hfun)
""",
        "Mock2 select the smooth-gauge extensionality theorem",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """attribute [-instance] Complex.addCommGroup
attribute [-instance] Complex.instRing

/-- Exact tangent formula for the cusp at zero. -/
""",
        """attribute [-instance] Complex.addCommGroup
attribute [-instance] Complex.instRing
attribute [-instance] Complex.instField

/-- Exact tangent formula for the cusp at zero. -/
""",
        "Mock2 Advanced select the densely normed field structure for reciprocals",
    )
    m2a = replace_exact(
        m2a,
        """attribute [instance] Complex.instRing
attribute [instance] Complex.addCommGroup
""",
        """attribute [instance] Complex.instField
attribute [instance] Complex.instRing
attribute [instance] Complex.addCommGroup
""",
        "Mock2 Advanced restore the canonical complex field structure",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  induction q using Quotient.inductionOn'
  simpa only [quotientNormSqDensity_mk] using
    upstairsNormSqDensity_nonneg M u _
""",
        """  induction q using Quotient.inductionOn'
  change 0 ≤ upstairsNormSqDensity M u _
  exact upstairsNormSqDensity_nonneg M u _
""",
        "FunctionalAnalysis expose the upstairs norm-density inequality",
    )
    fa = replace_exact(
        fa,
        """  induction q using Quotient.inductionOn'
  simp only [quotientNormSqDensity_mk, upstairsNormSqDensity_zero]
""",
        """  induction q using Quotient.inductionOn'
  change upstairsNormSqDensity M (0 : SmoothCompactWeightCore M) _ = 0
  exact upstairsNormSqDensity_zero M _
""",
        "FunctionalAnalysis expose the upstairs zero norm density",
    )
    fa = replace_exact(
        fa,
        """  simpa only [Function.comp_apply, quotientInnerDensity_mk] using hpull
""",
        """  change Integrable (upstairsInnerDensity M u v)
      (hyperbolicMeasure.restrict D.carrier) at hpull
  exact hpull
""",
        "FunctionalAnalysis identify the pulled-back quotient density definitionally",
    )
    quotient_replacements = [
        (
            """  induction q using Quotient.inductionOn'
  simpa only [quotientInnerDensity_mk] using
    upstairsInnerDensity_add_left M u v w _
""",
            """  induction q using Quotient.inductionOn'
  change upstairsInnerDensity M (u + v) w _ =
    upstairsInnerDensity M u w _ + upstairsInnerDensity M v w _
  exact upstairsInnerDensity_add_left M u v w _
""",
            "FunctionalAnalysis expose quotient additivity on the left",
        ),
        (
            """  induction q using Quotient.inductionOn'
  simpa only [quotientInnerDensity_mk] using
    upstairsInnerDensity_smul_left M c u v _
""",
            """  induction q using Quotient.inductionOn'
  change upstairsInnerDensity M (c • u) v _ =
    star c * upstairsInnerDensity M u v _
  exact upstairsInnerDensity_smul_left M c u v _
""",
            "FunctionalAnalysis expose quotient conjugate homogeneity",
        ),
        (
            """  induction q using Quotient.inductionOn'
  simpa only [quotientInnerDensity_mk] using
    upstairsInnerDensity_add_right M u v w _
""",
            """  induction q using Quotient.inductionOn'
  change upstairsInnerDensity M u (v + w) _ =
    upstairsInnerDensity M u v _ + upstairsInnerDensity M u w _
  exact upstairsInnerDensity_add_right M u v w _
""",
            "FunctionalAnalysis expose quotient additivity on the right",
        ),
        (
            """  induction q using Quotient.inductionOn'
  simpa only [quotientInnerDensity_mk] using
    upstairsInnerDensity_smul_right M c u v _
""",
            """  induction q using Quotient.inductionOn'
  change upstairsInnerDensity M u (c • v) _ =
    c * upstairsInnerDensity M u v _
  exact upstairsInnerDensity_smul_right M c u v _
""",
            "FunctionalAnalysis expose quotient homogeneity on the right",
        ),
        (
            """  induction q using Quotient.inductionOn'
  simpa only [quotientInnerDensity_mk] using
    upstairsInnerDensity_conj_symm M u v _
""",
            """  induction q using Quotient.inductionOn'
  change star (upstairsInnerDensity M v u _) =
    upstairsInnerDensity M u v _
  exact upstairsInnerDensity_conj_symm M u v _
""",
            "FunctionalAnalysis expose quotient Hermitian symmetry",
        ),
        (
            """  induction q using Quotient.inductionOn'
  simp only [quotientInnerDensity_mk, quotientNormSqDensity_mk,
    upstairsInnerDensity_self]
""",
            """  induction q using Quotient.inductionOn'
  change upstairsInnerDensity M u u _ =
    (upstairsNormSqDensity M u _ : ℂ)
  exact upstairsInnerDensity_self M u _
""",
            "FunctionalAnalysis expose the quotient diagonal density",
        ),
    ]
    for old, new, label in quotient_replacements:
        fa = replace_exact(fa, old, new, label)
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
