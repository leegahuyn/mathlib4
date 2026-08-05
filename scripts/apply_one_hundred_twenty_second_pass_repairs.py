from __future__ import annotations

from pathlib import Path

import apply_one_hundred_nineteenth_pass_repairs as pass119
import apply_one_hundred_twentieth_pass_repairs as pass120
import apply_one_hundred_twenty_first_pass_repairs as pass121
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def apply_replacements(path: Path, replacements: list[tuple[str, str, int, str]]) -> None:
    text = path.read_text(encoding="utf-8")
    changed = False
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """      have hnormSq :
          Complex.normSq (modularCircularArcParam t : ℂ) = 1 := by
        simp only [modularCircularArcParam, UpperHalfPlane.coe_mk,
          Complex.normSq_apply]
        nlinarith [hsqrt]
""",
            """      have hnormSq :
          Complex.normSq (modularCircularArcParam t : ℂ) = 1 := by
        simp only [modularCircularArcParam, UpperHalfPlane.coe_mk,
          Complex.normSq_apply]
        nlinarith [hsqrt]
      have hden :
          (t : ℝ) / 2 * ((t : ℝ) / 2) +
              Real.sqrt (1 - ((t : ℝ) / 2) ^ 2) *
                Real.sqrt (1 - ((t : ℝ) / 2) ^ 2) = 1 := by
        nlinarith [hsqrt]
""",
            1,
            "FunctionalAnalysis record the unit denominator on the circular edge",
        ),
        (
            """          modularTileEdgeParam, modularCircularArcParam, hnormSq]
""",
            """          modularTileEdgeParam, modularCircularArcParam, hnormSq, hden]
""",
            2,
            "FunctionalAnalysis simplify both circular pairing coordinates with the unit denominator",
        ),
        (
            """theorem modularBoundaryOrbit_smul_mem_iff
    (g : SL(2, ℤ)) (z : ℍ) :
    g • z ∈ modularBoundaryOrbit ↔ z ∈ modularBoundaryOrbit := by
  rw [← modularBoundaryOrbit_smul g,
    Set.mem_smul_set_iff_inv_smul_mem, inv_smul_smul]
""",
            """theorem modularBoundaryOrbit_smul_mem_iff
    (g : SL(2, ℤ)) (z : ℍ) :
    g • z ∈ modularBoundaryOrbit ↔ z ∈ modularBoundaryOrbit := by
  calc
    g • z ∈ modularBoundaryOrbit ↔
        g • z ∈ g • modularBoundaryOrbit := by rw [modularBoundaryOrbit_smul g]
    _ ↔ z ∈ modularBoundaryOrbit := by
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
""",
            1,
            "FunctionalAnalysis use orbit-set invariance in the correct membership orientation",
        ),
        (
            """  simpa only [hγ] using
    modularBoundaryOrbit_smul_mem_iff (γ : SL(2, ℤ)) z
""",
            """  rw [hγ z]
  exact modularBoundaryOrbit_smul_mem_iff (γ : SL(2, ℤ)) z
""",
            1,
            "FunctionalAnalysis rewrite the effective action pointwise",
        ),
        (
            """  have htile :
      gammaTwoCosetRep q • (g • z) ∈ gammaTwoClosedTileCarrier :=
    mem_gammaTwoClosedTileCarrier_iff.mpr
      ⟨q, g • z, hgfd, rfl⟩
  change ((γ⁻¹ : GammaTwo) : SL(2, ℤ)) • z ∈
    gammaTwoOpenCarrier
  rw [hcancel]
  exact htile
""",
            """  have htile :
      gammaTwoCosetRep q • (g • z) ∈ gammaTwoClosedTileCarrier :=
    mem_gammaTwoClosedTileCarrier_iff.mpr
      ⟨q, g • z, hgfd, rfl⟩
  simpa only [gammaTwoEffectiveElement_smul] using
    hcancel.symm ▸ htile
""",
            1,
            "FunctionalAnalysis keep the orbit-cover target in the closed carrier",
        ),
        (
            """  unfold gammaTwoNamedScalingHeightSublevel
  exact isClosed_iInter fun κ ↦
    isClosed_le (gammaTwoCuspHeight_continuous κ) continuous_const
""",
            """  unfold gammaTwoNamedScalingHeightSublevel
  rw [show {z : ℍ | ∀ κ : GammaTwoCusp,
      gammaTwoCuspHeight κ z ≤ gammaTwoCuspLevel Y} =
      ⋂ κ : GammaTwoCusp,
        {z : ℍ | gammaTwoCuspHeight κ z ≤ gammaTwoCuspLevel Y} by
    ext z
    simp]
  exact isClosed_iInter fun κ ↦
    isClosed_le (gammaTwoCuspHeight_continuous κ) continuous_const
""",
            1,
            "FunctionalAnalysis expose the universal height predicate as an intersection",
        ),
        (
            """  exact isClosed_iUnion_of_finite fun q ↦
    ModularGroup.isClosed_fd.smul (gammaTwoCosetRep q)
""",
            """  exact isClosed_iUnion_of_finite fun q ↦ by
    let g : SL(2, ℤ) := gammaTwoCosetRep q
    have hset :
        g • ModularGroup.fd =
          (fun z : ℍ => g⁻¹ • z) ⁻¹' ModularGroup.fd := by
      ext z
      constructor
      · intro hz
        rcases Set.mem_smul_set.mp hz with ⟨w, hw, rfl⟩
        simpa using hw
      · intro hz
        exact Set.mem_smul_set.mpr ⟨g⁻¹ • z, hz, by simp⟩
    rw [hset]
    exact ModularGroup.isClosed_fd.preimage
      (HalfIntegralMultiplier.continuous_sl2z_smul g⁻¹)
""",
            1,
            "FunctionalAnalysis prove closedness of each translated modular tile by preimage",
        ),
        (
            """  UpperHalfPlane.continuous_im.comp
    (continuous_const_smul (gammaTwoCosetRep q)⁻¹)
""",
            """  UpperHalfPlane.continuous_im.comp
    (HalfIntegralMultiplier.continuous_sl2z_smul (gammaTwoCosetRep q)⁻¹)
""",
            1,
            "FunctionalAnalysis use the explicit continuous integral modular action",
        ),
        (
            """  exact ∑ q in Finset.univ.filter (fun q : GammaTwoRightCoset ↦
    gammaTwoTileCuspClass q = κ), gammaTwoTileHeight q z
""",
            """  exact Finset.sum
    (Finset.univ.filter (fun q : GammaTwoRightCoset ↦
      gammaTwoTileCuspClass q = κ))
    (fun q => gammaTwoTileHeight q z)
""",
            1,
            "FunctionalAnalysis replace unsupported term-mode binder syntax with Finset.sum",
        ),
    ])


def main() -> int:
    pass119.main()
    pass120.repair_mock1_advanced()
    pass120.repair_mock2()
    pass121.repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
