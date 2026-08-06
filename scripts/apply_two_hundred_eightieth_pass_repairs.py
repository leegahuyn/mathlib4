from __future__ import annotations

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


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """  have hcompat : F.CompatibleFamily D sf := by
    intro i j
    simpa [D, toMathlibPresheaf] using hsf i j
  obtain ⟨s, hs, huniq⟩ := hF.existsUnique_gluing D sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    simpa [D, toMathlibPresheaf] using hs i
  · intro t ht
    apply huniq t
    intro i
    simpa [D, toMathlibPresheaf] using ht i
""",
        """  have hcompat : F.CompatibleFamily D sf := by
    intro i j
    simpa only [toMathlibPresheaf_map_apply] using hsf i j
  obtain ⟨s, hs, huniq⟩ := hF.existsUnique_gluing D sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    simpa only [toMathlibPresheaf_map_apply] using hs i
  · intro t ht
    apply huniq t
    intro i
    simpa only [toMathlibPresheaf_map_apply] using ht i
""",
        "Mock2 transport sheaf gluing only through the map-evaluation lemma",
    )
    m2 = replace_exact(
        m2,
        """theorem actualProposition20_certificate : ActualProposition20Certificate C where
""",
        """noncomputable def actualProposition20_certificate : ActualProposition20Certificate C where
""",
        "Mock2 make the data-valued Proposition 20 certificate a definition",
    )
    m2 = replace_exact(
        m2,
        """theorem checklist_8_P1_unconditional :
    ActualProposition20Certificate AdaptedGeometryCover.canonical :=
""",
        """noncomputable def checklist_8_P1_unconditional :
    ActualProposition20Certificate AdaptedGeometryCover.canonical :=
""",
        "Mock2 make the data-valued checklist closure a definition",
    )
    m2 = replace_exact(
        m2,
        """structure FiniteCoverSheafAxioms
    {I : Type u} [Fintype I] (D : FiniteCoverSheafData.{u, v} I) : Prop where
""",
        """structure FiniteCoverSheafAxioms
    {I : Type u} [Fintype I] (D : FiniteCoverSheafData.{u, v} I) : Type (max u v) where
""",
        "Mock2 place finite-cover gluing data in Type rather than Prop",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  letI : Countable Gamma2Element :=
    Countable.of_injective
      (fun γ : Gamma2Element => encodeMatrix γ.1.1) (by
        intro γ δ h
        apply Subtype.ext
        apply Subtype.ext
        exact encodeMatrix_injective h)
""",
        """  letI : Countable Gamma2Element :=
    (show Function.Injective
        (fun γ : Gamma2Element => encodeMatrix γ.1.1) by
      intro γ δ h
      apply Subtype.ext
      apply Subtype.ext
      exact encodeMatrix_injective h).countable
""",
        "Mock2 Advanced derive Gamma2 countability from the injective encoding",
    )
    m2a = replace_exact(
        m2a,
        """  simpa only [Function.comp_def,
    Set.preimage_image_eq _ UpperHalfPlane.coe_injective] using h
""",
        """  change IntegrableOn
    (fun x : UpperHalfPlane => fdHeightMajorant ((x : ℂ).im))
    ModularGroup.fd (volume.comap UpperHalfPlane.coe)
  exact h
""",
        "Mock2 Advanced retain the explicit coerced imaginary-part function",
    )
    m2a = replace_exact(
        m2a,
        """  intro τ hτ
  simp only [fdHeightMajorant, NNReal.smul_def, NNReal.coe_pow,
    NNReal.coe_inv, NNReal.coe_mk] <;> ring
""",
        """  intro τ hτ
  change
    (1 + Real.sqrt τ.im) * (1 / τ.im) ^ 2 =
      (1 / τ.im) ^ 2 * (1 + Real.sqrt τ.im)
  ring
""",
        "Mock2 Advanced compare the hyperbolic density in a cast-free real normal form",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  rw [inner_self_eq_norm_sq (𝕜 := ℂ) x]
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)
""",
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  rw [← norm_sq_eq_re_inner]
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)
""",
        "FunctionalAnalysis rewrite the real inner self from the norm-square theorem",
    )
    fa = replace_exact(
        fa,
        """  intro y
  rw [Q.graphExtension_coe y]
  rfl
""",
        """  intro y
  rw [Q.graphExtension_coe y]
  calc
    ‖(y : EnergyTarget H₀ HR HL)‖ = ‖y‖ := rfl
    _ = ‖(y : Q.SobolevCompletion)‖ :=
      (UniformSpace.Completion.norm_coe y).symm
""",
        "FunctionalAnalysis compare the ambient and completion norms through the core norm",
    )
    fa = replace_exact(
        fa,
        """    _ = ‖Q.baseExtension x‖ ^ 2 +
        ‖Q.raiseExtension x‖ ^ 2 + ‖Q.lowerExtension x‖ ^ 2 := by
      ring
""",
        """    _ = ‖Q.baseExtension x‖ ^ 2 +
        ‖Q.raiseExtension x‖ ^ 2 + ‖Q.lowerExtension x‖ ^ 2 := by
      ring_nf
""",
        "FunctionalAnalysis normalize the completed graph sum of squares",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
