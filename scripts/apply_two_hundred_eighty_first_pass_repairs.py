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
        """  have hcompat : F.CompatibleFamily D sf := by
    intro i j
    have hij := hsf i j
    rw [toMathlibPresheaf_map_apply, toMathlibPresheaf_map_apply] at hij
    simpa only [D] using hij
  obtain ⟨s, hs, huniq⟩ := hF.existsUnique_gluing D sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    change F.res (le_iSup U i) s = sf i
    exact hs i
  · intro t ht
    apply huniq t
    intro i
    have hti := ht i
    rw [toMathlibPresheaf_map_apply] at hti
    change F.res (le_iSup U i) t = sf i
    exact hti
""",
        "Mock2 evaluate categorical restriction maps before custom gluing transport",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  change IntegrableOn
    (fun x : UpperHalfPlane => fdHeightMajorant ((x : ℂ).im))
    ModularGroup.fd (volume.comap UpperHalfPlane.coe)
  exact h
""",
        """  simpa only [Function.comp_apply,
    Set.preimage_image_eq _ UpperHalfPlane.coe_injective] using h
""",
        "Mock2 Advanced simplify both the composed function and the embedded cell",
    )
    m2a = replace_exact(
        m2a,
        """theorem integralMatrixAction_measurableEmbedding
    (g : Gamma2SixCellPolygon.IntegralSpecialLinear) :
    MeasurableEmbedding (fun τ : UpperHalfPlane => g • τ) :=
  (Homeomorph.smul g).measurableEmbedding
""",
        """theorem integralMatrixAction_measurableEmbedding
    (g : Gamma2SixCellPolygon.IntegralSpecialLinear) :
    MeasurableEmbedding (fun τ : UpperHalfPlane => g • τ) := by
  simpa only [MulAction.compHom_smul_def] using
    (Homeomorph.smul
      ((Matrix.SpecialLinearGroup.mapGL
        (n := Fin 2) (R := ℤ) ℝ) g)).measurableEmbedding
""",
        "Mock2 Advanced transport the measurable embedding through the real matrix action",
    )
    m2a = replace_exact(
        m2a,
        """    have hc' :
        AEStronglyMeasurable (cellPullback ρ r) hyperbolicMeasure := by
      simpa [cellPullback, Function.comp_def] using hc
""",
        """    have hc' :
        AEStronglyMeasurable (cellPullback ρ r) hyperbolicMeasure := by
      change AEStronglyMeasurable
        (fun x => ρ ((Gamma2SixCellPolygon.repMatrix r)⁻¹ • x))
        hyperbolicMeasure
      exact hc
""",
        "Mock2 Advanced unfold the cell pullback without changing the action instance",
    )
    m2a = replace_exact(
        m2a,
        """  MemLp.ae_eq (positiveNormalizedRepresentative_add u v).symm
    (hu.add hv)
""",
        """  MemLp.ae_eq (positiveNormalizedRepresentative_add u v).symm
    (MemLp.add hu hv)
""",
        "Mock2 Advanced select the MemLp addition theorem in the positive convention",
    )
    m2a = replace_exact(
        m2a,
        """  MemLp.ae_eq (positiveNormalizedRepresentative_smul c u).symm
    (hu.const_smul c)
""",
        """  MemLp.ae_eq (positiveNormalizedRepresentative_smul c u).symm
    (MemLp.const_smul hu c)
""",
        "Mock2 Advanced select the MemLp scalar theorem in the positive convention",
    )
    m2a = replace_exact(
        m2a,
        """  MemLp.ae_eq (inverseNormalizedRepresentative_add u v).symm
    (hu.add hv)
""",
        """  MemLp.ae_eq (inverseNormalizedRepresentative_add u v).symm
    (MemLp.add hu hv)
""",
        "Mock2 Advanced select the MemLp addition theorem in the inverse convention",
    )
    m2a = replace_exact(
        m2a,
        """  MemLp.ae_eq (inverseNormalizedRepresentative_smul c u).symm
    (hu.const_smul c)
""",
        """  MemLp.ae_eq (inverseNormalizedRepresentative_smul c u).symm
    (MemLp.const_smul hu c)
""",
        "Mock2 Advanced select the MemLp scalar theorem in the inverse convention",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  rw [← norm_sq_eq_re_inner]
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)
""",
        """theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  have hs : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  simpa [inner_self_eq_norm_sq_to_K] using hs
""",
        "FunctionalAnalysis simplify the complex inner self through its exact norm square",
    )
    fa = replace_exact(
        fa,
        """    _ = ‖Q.baseExtension x‖ ^ 2 +
        ‖Q.raiseExtension x‖ ^ 2 + ‖Q.lowerExtension x‖ ^ 2 := by
      ring_nf
""",
        """    _ = ‖Q.baseExtension x‖ ^ 2 +
        ‖Q.raiseExtension x‖ ^ 2 + ‖Q.lowerExtension x‖ ^ 2 := by
      change
        ‖(Q.graphExtension x).fst‖ ^ 2 +
            ‖(Q.graphExtension x).snd.fst‖ ^ 2 +
              ‖(Q.graphExtension x).snd.snd‖ ^ 2 =
          ‖(Q.graphExtension x).fst‖ ^ 2 +
            ‖(Q.graphExtension x).snd.fst‖ ^ 2 +
              ‖(Q.graphExtension x).snd.snd‖ ^ 2
      rfl
""",
        "FunctionalAnalysis expose the three completed graph projections definitionally",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
