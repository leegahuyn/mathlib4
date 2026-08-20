from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "04c17e889dcbd0283ed7c2a7c7aa7a888dbe42b20a50d8dbf1db51d6568a6f62"
EXPECTED_OUTPUT_SHA256 = "8fd20f88c43060d392bab969c91a84b7c0bb08657af7728752a77c5f3c57c6c6"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrence(s), found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass358] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass358 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(text,
        """    _ = 0 := by
      simp
""",
        """    _ = 0 := by
      exact ContinuousLinearMap.opNorm_zero
""",
        "FunctionalAnalysis zero operator norm")

    text = replace_exact(text,
        """  change
    inverseEtaPaperOrbitDenom γ z ^ (n * 2) *
          fixedPhaseIntegralWeightFactor n z *
        (inverseEtaMultiplier GammaTwo).factor γ z *
          inverseEtaSection z =
      fixedPhaseIntegralWeightFactor n z * inverseEtaSection z *
        (inverseEtaMultiplier GammaTwo).factor γ z *
          inverseEtaPaperOrbitDenom γ z ^ (2 * n)
  rw [mul_comm n 2]
  ring
""",
        """  ring
""",
        "FunctionalAnalysis all-index seed covariance")

    text = replace_exact(text,
        """noncomputable def reindexedActualLower (n : ℤ) :
    InverseEtaFixedPhaseCore (n + 1) →ₗ[ℂ]
      InverseEtaFixedPhaseCore n := by
  simpa only [add_sub_cancel_right] using
    (InverseEtaFixedPhaseCore.lower (n + 1))

/-- The transported actual lowering map is exactly the separately typed
`lowerFromSucc`; both have the same raw differential expression and stable-core
proof. -/
theorem reindexedActualLower_eq_lowerFromSucc (n : ℤ) :
    reindexedActualLower n = InverseEtaFixedPhaseCore.lowerFromSucc n := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  rfl
""",
        """noncomputable def reindexedActualLower (n : ℤ) :
    InverseEtaFixedPhaseCore (n + 1) →ₗ[ℂ]
      InverseEtaFixedPhaseCore n :=
  InverseEtaFixedPhaseCore.lowerFromSucc n

/-- The transported actual lowering map is exactly the separately typed
`lowerFromSucc`; both have the same raw differential expression and stable-core
proof. -/
theorem reindexedActualLower_eq_lowerFromSucc (n : ℤ) :
    reindexedActualLower n = InverseEtaFixedPhaseCore.lowerFromSucc n :=
  rfl
""",
        "FunctionalAnalysis canonical reindexed lowering")

    text = replace_exact(text,
        """theorem successorGraphCoordinates_eq_coordinates (n : ℤ) :
    successorGraphCoordinates n =
      (by
        simpa only [add_sub_cancel_right] using
          (DefinitionOneSobolev.FixedPhaseGraphCompletion.coordinates
            (n + 1))) := by
  simp only [successorGraphCoordinates,
    reindexedActualLoweredCoordinate, reindexedActualLower,
    DefinitionOneSobolev.FixedPhaseGraphCompletion.coordinates,
    loweredCoordinate, add_sub_cancel_right]
""",
        """theorem successorGraphCoordinates_eq_coordinates (n : ℤ) :
    successorGraphCoordinates n =
      (by
        have hIndex : n + 1 - 1 = n := add_sub_cancel_right n 1
        exact hIndex ▸
          (DefinitionOneSobolev.FixedPhaseGraphCompletion.coordinates
            (n + 1))) := by
  have hIndex : n + 1 - 1 = n := add_sub_cancel_right n 1
  change successorGraphCoordinates n =
    hIndex ▸
      (DefinitionOneSobolev.FixedPhaseGraphCompletion.coordinates (n + 1))
  cases hIndex
  apply DefinitionOneSobolev.QuotientHilbertCoordinates.ext
  · rfl
  · rfl
  · apply LinearMap.ext
    intro u
    apply Subtype.ext
    rfl
""",
        "FunctionalAnalysis successor-coordinate transport")

    text = replace_exact(text,
        """  rw [(successorGraphCoordinates n)
      .range_graphExtension_eq_closure_range_graph]
""",
        """  rw [(successorGraphCoordinates n).range_graphExtension_eq_closure_range_graph]
""",
        "FunctionalAnalysis graph-extension dot notation")

    text = replace_exact(text,
        """theorem coordinates_jointlyClosable (n : ℤ) :
    (DefinitionOneSobolev.FixedPhaseGraphCompletion.coordinates n).JointlyClosable := by
  simpa only [sub_add_cancel] using
    (coordinates_add_one_jointlyClosable (n - 1))
""",
        """theorem coordinates_jointlyClosable (n : ℤ) :
    (DefinitionOneSobolev.FixedPhaseGraphCompletion.coordinates n).JointlyClosable := by
  have hIndex : n - 1 + 1 = n := sub_add_cancel n 1
  exact hIndex ▸ coordinates_add_one_jointlyClosable (n - 1)
""",
        "FunctionalAnalysis coordinates closability transport")

    text = replace_exact(text,
        """  have hFormal :=
    physicalLowerFromSucc_isFormalAdjoint_negativeRaise hGreen
      (l2CoreRangeEquiv (n + 1) v) (l2CoreRangeEquiv n u)
  rw [physicalLowerFromSucc_on_core, LinearPMap.neg_apply,
    physicalRaise_on_core, l2CoreRangeEquiv_coe] at hFormal
  simpa only [inner_neg_right] using hFormal
""",
        """  have hCore :=
    (physicalGreenIdentityAt_iff_coreInner n).mp hGreen u v
  have hConj := congrArg (starRingEnd ℂ) hCore
  simp only [map_add, map_zero, starRingEnd_apply,
    inner_conj_symm] at hConj
  linear_combination hConj
""",
        "FunctionalAnalysis lowering formal-adjoint core identity")

    text = replace_exact(text,
        """noncomputable def graphLowerFromSuccExtension (n : ℤ) :
    GraphSobolevCompletion (n + 1) →L[ℂ]
      OrbitPeterssonHilbert n := by
  have hIndex : n + 1 - 1 = n := by omega
  rw [← hIndex]
  exact lowerExtension (n + 1)
""",
        """noncomputable def graphLowerFromSuccExtension (n : ℤ) :
    GraphSobolevCompletion (n + 1) →L[ℂ]
      OrbitPeterssonHilbert n := by
  have hIndex : n + 1 - 1 = n := add_sub_cancel_right n 1
  exact hIndex ▸ lowerExtension (n + 1)
""",
        "FunctionalAnalysis graph lowering extension transport")

    text = replace_exact(text,
        """theorem gammaTwoOpenTiles_pairwiseDisjoint :
    Pairwise (Disjoint on fun q : GammaTwoRightCoset =>
      gammaTwoCosetRep q • ModularGroup.fdo) := by
""",
        """theorem gammaTwoOpenTiles_pairwiseDisjoint :
    Pairwise (fun q₁ q₂ : GammaTwoRightCoset =>
      Disjoint (gammaTwoCosetRep q₁ • ModularGroup.fdo)
        (gammaTwoCosetRep q₂ • ModularGroup.fdo)) := by
""",
        "FunctionalAnalysis pairwise open tiles")

    text = replace_exact(text,
        """theorem gammaTwoOpenTile_measurable (q : GammaTwoRightCoset) :
    MeasurableSet (gammaTwoCosetRep q • ModularGroup.fdo) :=
  (ModularGroup.isOpen_fdo.smul (gammaTwoCosetRep q)).measurableSet
""",
        """theorem gammaTwoOpenTile_measurable (q : GammaTwoRightCoset) :
    MeasurableSet (gammaTwoCosetRep q • ModularGroup.fdo) := by
  change MeasurableSet
    (((gammaTwoCosetRep q : SL(2, ℤ)) : GL (Fin 2) ℝ) •
      ModularGroup.fdo)
  exact
    (ModularGroup.isOpen_fdo.smul
      (((gammaTwoCosetRep q : SL(2, ℤ)) : GL (Fin 2) ℝ))).measurableSet
""",
        "FunctionalAnalysis measurable open tile")

    text = replace_exact(text,
        """    (fun q => hf.mono_set (Set.subset_iUnion _ q))
""",
        """    (fun q => hf.mono_set
      (Set.subset_iUnion
        (fun q : GammaTwoRightCoset =>
          gammaTwoCosetRep q • ModularGroup.fdo) q))
""",
        "FunctionalAnalysis explicit selected-tile union")

    text = replace_exact(text,
        """def hyperbolicDensityNNReal (z : ℍ) : ℝ≥0 :=
  (1 / NNReal.mk z.im z.im_pos.le) ^ 2
""",
        """def hyperbolicDensityNNReal (z : ℍ) : ℝ≥0 :=
  (1 / NNReal.mk z.im (le_of_lt z.im_pos)) ^ 2
""",
        "FunctionalAnalysis hyperbolic density proof")

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass358 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass358] FunctionalAnalysis first transport, graph, tile, and density roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
