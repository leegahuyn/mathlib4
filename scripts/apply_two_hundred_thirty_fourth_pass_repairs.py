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
        """noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] E_G)
  infer_instance

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        """noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] E_G)
  infer_instance

noncomputable local instance oneFormValueChartedSpace :
    ChartedSpace (OneFormValue I_G G) (OneFormValue I_G G) :=
  chartedSpaceSelf (OneFormValue I_G G)

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        "Mock2 register the one-form value self chart directly",
    )
    m2 = replace_exact(
        m2,
        """  smooth_toFun :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] E_G) ∞ toFun
""",
        """  smooth_toFun :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞ toFun
""",
        "Mock2 use the registered one-form self chart",
    )
    m2 = replace_exact(
        m2,
        """    exact (contMDiff_const :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] E_G) ∞
        (fun _ : coverOpen U => (0 : OneFormValue I_G G)))
""",
        """    exact (contMDiff_const :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞
        (fun _ : coverOpen U => (0 : OneFormValue I_G G)))
""",
        "Mock2 use the one-form self chart for the zero section",
    )
    m2 = replace_exact(
        m2,
        """/-- Mathlib's local smoothness predicate, specialized to `𝔤`-valued
one-form coefficients on the upper half-plane. -/
def strictSmoothOneFormLocalPredicate :
    TopCat.LocalPredicate.{uEG, 0}
      (fun _ : TopCat.of H => OneFormValue I_G G) :=
  (contDiffWithinAt_localInvariantProp
    (I := 𝓘(ℂ))
    (I' := 𝓘(ℂ, OneFormValue I_G G)) ∞).localPredicate
      H (OneFormValue I_G G)
""",
        """/-- Restriction-stable smoothness of one-form-valued functions. -/
def strictSmoothOneFormPrelocalPredicate :
    TopCat.PrelocalPredicate.{uEG, 0}
      (fun _ : TopCat.of H => OneFormValue I_G G) where
  pred {U} f :=
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞ f
  res {U V} i f hf := by
    intro x
    exact (hf (i x)).comp x ((contMDiff_inclusion i.le) x)

/-- The universe-polymorphic local smoothness predicate obtained by
sheafifying restriction-stable `ContMDiff`. -/
def strictSmoothOneFormLocalPredicate :
    TopCat.LocalPredicate.{uEG, 0}
      (fun _ : TopCat.of H => OneFormValue I_G G) :=
  (strictSmoothOneFormPrelocalPredicate I_G G).sheafify
""",
        "Mock2 replace the same-universe smooth local predicate",
    )
    m2 = replace_exact(
        m2,
        """theorem strictGluedToFun_contMDiff {iota : Type}
    (C : OpenCoverData X iota)
    (s : (liftedFormPresheaf I_G G).CoverSectionProduct C)
    (hs : (liftedFormPresheaf I_G G).CompatibleFamily C s) :
    ContMDiff 𝒤(ℂ) 𝒤(ℂ, OneFormValue I_G G) ∞
      (strictGluedToFun I_G G C s) := by
  change (strictSmoothOneFormLocalPredicate I_G G).pred
    (strictGluedToFun I_G G C s)
  apply (strictSmoothOneFormLocalPredicate I_G G).locality
  intro tau
  let i := strictGlueIndex C tau
  refine ⟨coverOpen (C.piece i), strictGlueIndex_mem C tau,
    homOfLE (coverOpen_mono (C.piece_le_target i)), ?_⟩
  change ContMDiff 𝒤(ℂ) 𝒤(ℂ, OneFormValue I_G G) ∞
    (fun x : coverOpen (C.piece i) =>
      strictGluedToFun I_G G C s
        (SmoothOneForm.coverInclusion (C.piece_le_target i) x))
  apply (s i).smooth_toFun.congr
  intro x
  exact strictGluedToFun_eq_on_piece I_G G C s hs i x
""",
        """theorem strictGluedToFun_contMDiff {iota : Type}
    (C : OpenCoverData X iota)
    (s : (liftedFormPresheaf I_G G).CoverSectionProduct C)
    (hs : (liftedFormPresheaf I_G G).CompatibleFamily C s) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞
      (strictGluedToFun I_G G C s) := by
  intro tau
  let i := strictGlueIndex C tau
  let tau_i : coverOpen (C.piece i) :=
    ⟨(tau : H), strictGlueIndex_mem C tau⟩
  have hlocal :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞
        (fun x : coverOpen (C.piece i) =>
          strictGluedToFun I_G G C s
            (SmoothOneForm.coverInclusion (C.piece_le_target i) x)) := by
    apply (s i).smooth_toFun.congr
    intro x
    exact strictGluedToFun_eq_on_piece I_G G C s hs i x
  have htau :
      SmoothOneForm.coverInclusion (C.piece_le_target i) tau_i = tau := by
    apply Subtype.ext
    rfl
  rw [← htau]
  rw [(contDiffWithinAt_localInvariantProp
    (I := 𝓘(ℂ))
    (I' := 𝓘(ℂ, OneFormValue I_G G)) ∞).liftPropAt_iff_comp_inclusion
      (coverOpen_mono (C.piece_le_target i))]
  exact hlocal tau_i
""",
        "Mock2 prove strict glued smoothness directly from local inclusions",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  have hne : -cuspHorizontalAmbientCurve Y x ≠ 0 :=
    neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        """  have hne : -cuspHorizontalAmbientCurve Y x ≠ 0 :=
    neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  have hspace :
      (NormedAlgebra.toNormedSpace ℂ : NormedSpace ℝ ℂ) =
        NormedSpace.complexToReal := Subsingleton.elim _ _
  cases hspace
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        "Mock2 Advanced transport the real complex normed-space proof",
    )
    m2a = replace_exact(
        m2a,
        """  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun x : ℝ => (-cuspHorizontalAmbientCurve Y x)⁻¹)
  exact hneg.inv (fun x => neg_ne_zero.mpr
    (cuspHorizontalAmbientCurve_ne_zero hY x))
""",
        """  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun x : ℝ => (-cuspHorizontalAmbientCurve Y x)⁻¹)
  have hspace :
      (NormedAlgebra.toNormedSpace ℂ : NormedSpace ℝ ℂ) =
        NormedSpace.complexToReal := Subsingleton.elim _ _
  cases hspace
  exact hneg.inv (fun x => neg_ne_zero.mpr
    (cuspHorizontalAmbientCurve_ne_zero hY x))
""",
        "Mock2 Advanced transport reciprocal smoothness across normed-space proofs",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """    simp only [map_add, map_mul, Complex.conj_I,
      conj_exponentC, conj_rpowScale]
""",
        """    simp only [star_add, star_mul, Complex.conj_I,
      conj_exponentC, conj_rpowScale]
""",
        "FunctionalAnalysis expand star over raising addition and multiplication",
    )
    fa = replace_exact(
        fa,
        """  rw [weightedConjugate_raise_eq_flux, dx, dy,
    compactPair_add_left, compactPair_smul_left,
    compactPair_directionalDerivative_left,
    compactPair_directionalDerivative_left,
    compactPair_add_right, compactPair_smul_right]
""",
        """  rw [weightedConjugate_raise_eq_flux, dx, dy, normalizedLower,
    compactPair_add_left, compactPair_smul_left,
    compactPair_directionalDerivative_left,
    compactPair_directionalDerivative_left,
    compactPair_add_right, compactPair_smul_right]
""",
        "FunctionalAnalysis expose normalized lowering in the Green identity",
    )
    fa = replace_exact(
        fa,
        """    simp only [map_add, map_mul, map_neg, Complex.conj_I,
      conj_exponentC, conj_rpowScale]
""",
        """    simp only [star_add, star_mul, star_neg, Complex.conj_I,
      conj_exponentC, conj_rpowScale]
""",
        "FunctionalAnalysis expand star over normalized lowering",
    )
    fa = replace_exact(
        fa,
        """  rw [weightedConjugate_normalizedLower_eq_flux, dx, dy,
    compactPair_add_left, compactPair_add_left,
    compactPair_smul_left,
    compactPair_directionalDerivative_left,
    compactPair_directionalDerivative_left,
    compactPair_smul_left,
    compactPair_rpowMul_left_eq_right,
    compactPair_add_right, compactPair_add_right,
    compactPair_smul_right, compactPair_smul_right]
""",
        """  rw [weightedConjugate_normalizedLower_eq_flux, dx, dy, raise,
    compactPair_add_left, compactPair_add_left,
    compactPair_smul_left,
    compactPair_directionalDerivative_left,
    compactPair_directionalDerivative_left,
    compactPair_smul_left,
    compactPair_rpowMul_left_eq_right,
    compactPair_add_right, compactPair_add_right,
    compactPair_smul_right, compactPair_smul_right]
""",
        "FunctionalAnalysis expose raising in the lowering Green identity",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
