from __future__ import annotations

from pathlib import Path

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


def replace_block(path: Path, start: str, end: str, replacement: str, label: str) -> None:
    text = path.read_text(encoding="utf-8")
    if text.count(start) != 1 or text.count(end) != 1:
        raise RuntimeError(
            f"{label}: expected unique markers, found start={text.count(start)}, end={text.count(end)}"
        )
    i = text.index(start)
    j = text.index(end, i)
    path.write_text(text[:i] + replacement + text[j:], encoding="utf-8", newline="\n")
    print(f"{label}: applied 1")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    apply_replacements(path, [
        (
            "    simpa only [TensorProduct.map_tmul, tensorRestriction_tmul, hpot, hframe]\n",
            "    rw [tensorRestriction_tmul, hpot]\n",
            1,
            "Mock2 reduce the remaining inner tensor restriction in nabla naturality",
        ),
        (
            "    simpa only [TensorProduct.map_tmul, tensorRestriction_tmul, hlog, hframe]\n",
            "    rw [tensorRestriction_tmul, hlog]\n",
            1,
            "Mock2 reduce the remaining inner tensor restriction in logarithmic naturality",
        ),
    ])
    replace_block(
        path,
        "theorem Dq_restrict {E F : ModuleCat ℂ}\n",
        "/-! ### Complex linearity and the full scalar Leibniz rule -/\n",
        """theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  have hn := nablaTensorId_restrict (X := X) P hUV z
  have hi := idTensorDq_restrict (X := X) P hUV z
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (nablaTensorId P V z + idTensorDq P V z) =
      nablaTensorId P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) +
        idTensorDq P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z)
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (nablaTensorId P V z) =
      nablaTensorId P U
        (tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV z) at hn
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (idTensorDq P V z) =
      idTensorDq P U
        (tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV z) at hi
  calc
    _ = tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
          (nablaTensorId P V z) +
        tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
          (idTensorDq P V z) :=
      (tensorRestriction (aqPresheaf E F)
        (omega1Presheaf (X := X)) hUV).map_add _ _
    _ = _ := congrArg₂ (· + ·) hn hi

""",
        "Mock2 derive full Dq naturality through raw tensor restrictions",
    )


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  · rintro ⟨z, hz⟩
    rw [← hz]
    simp [crtObstructionMap, comparisonMap_apply,
      ZMod.castHom_apply, ZMod.cast_intCast]
""",
            """  · rintro ⟨z, hz⟩
    rw [← hz]
    change
      (ZMod.cast (z : ZMod M) : ZMod (Nat.gcd M N)) -
        (ZMod.cast (z : ZMod N) : ZMod (Nat.gcd M N)) = 0
    rw [ZMod.cast_intCast (Nat.gcd_dvd_left M N),
      ZMod.cast_intCast (Nat.gcd_dvd_right M N)]
    exact sub_self _
""",
            1,
            "Mock2Advanced prove the reverse CRT obstruction implication explicitly",
        ),
        (
            """theorem cyclicFreeComplex_d_comp_augmentation (N : ℕ) :
    (cyclicFreeComplex N).d 1 0 ≫
      ModuleCat.ofHom
        (cyclicResolutionAugmentation N).toIntLinearMap = 0 := by
  rw [cyclicFreeComplex_d_one_zero]
  apply ModuleCat.hom_ext
  ext z
  simp [cyclicResolutionDifferential, cyclicResolutionAugmentation]
""",
            """theorem cyclicFreeComplex_d_comp_augmentation (N : ℕ) :
    (cyclicFreeComplex N).d 1 0 ≫
      ModuleCat.ofHom
        (cyclicResolutionAugmentation N).toIntLinearMap = 0 := by
  rw [cyclicFreeComplex_d_one_zero]
  apply ModuleCat.hom_ext
  ext
  change cyclicResolutionAugmentation N
      (cyclicResolutionDifferential N 1) = 0
  exact (cyclicResolution_exact N _).2 ⟨1, rfl⟩
""",
            1,
            "Mock2Advanced prove differential-augmentation composition from exactness",
        ),
        (
            """theorem cyclicFreeAugmentation_f_zero (N : ℕ) :
    (cyclicFreeAugmentation N).f 0 =
      ModuleCat.ofHom
        (cyclicResolutionAugmentation N).toIntLinearMap := by
  simp [cyclicFreeAugmentation]
""",
            """theorem cyclicFreeAugmentation_f_zero (N : ℕ) :
    (cyclicFreeAugmentation N).f 0 =
      ModuleCat.ofHom
        (cyclicResolutionAugmentation N).toIntLinearMap := by
  unfold cyclicFreeAugmentation
  rfl
""",
            1,
            "Mock2Advanced expose the degree-zero augmentation definitionally",
        ),
        (
            """theorem cyclicPresentationShortComplex_exact (N : ℕ) :
    (cyclicPresentationShortComplex N).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).2
  simpa [cyclicPresentationShortComplex] using cyclicResolution_exact N
""",
            """theorem cyclicPresentationShortComplex_exact (N : ℕ) :
    (cyclicPresentationShortComplex N).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro z hz
  exact (cyclicResolution_exact N z).1 hz
""",
            1,
            "Mock2Advanced prove short-complex exactness on the concrete carrier",
        ),
        (
            """theorem cyclicPresentationShortComplex_epi (N : ℕ) :
    Epi (cyclicPresentationShortComplex N).g := by
  apply (ModuleCat.epi_iff_surjective _).2
  simpa [cyclicPresentationShortComplex] using
    cyclicResolutionAugmentation_surjective N
""",
            """theorem cyclicPresentationShortComplex_epi (N : ℕ) :
    Epi (cyclicPresentationShortComplex N).g := by
  apply (ModuleCat.epi_iff_surjective _).2
  intro z
  exact cyclicResolutionAugmentation_surjective N z
""",
            1,
            "Mock2Advanced prove the augmentation epi pointwise",
        ),
    ])


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    apply_replacements(path, [
        (
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le
    (show (2 : ℕ∞ω) ≤ ∞ by simp)
""",
            """  (RealSmooth.contDiffAt_upperLift hu z).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
""",
            1,
            "FunctionalAnalysis compare finite order with inner infinity",
        ),
        (
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (show minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) by
      simp [minSmoothness])).iteratedFDeriv_cons
""",
            """  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by
      simpa only [minSmoothness] using
        (WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ from le_top)))).iteratedFDeriv_cons
""",
            1,
            "FunctionalAnalysis compare minimum smoothness with inner infinity",
        ),
        (
            """  simp only [raiseRaw, lowerRaw, map_add, map_mul, map_neg,
    map_pow, star_div, Complex.conj_I, conj_physicalExponent,
    conj_heightC]
  field_simp [hh] <;> ring
""",
            """  simp only [raiseRaw, lowerRaw, star_add, star_mul', star_inv₀,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
  field_simp [hh] <;> ring
""",
            1,
            "FunctionalAnalysis expand conjugation throughout the Green identity",
        ),
    ])
    text = path.read_text(encoding="utf-8")
    old = """  rw [mixedDerivative_comm hf z, sub_self, mul_zero, add_zero] at h
  linear_combination h
"""
    if text.count(old) != 2:
        raise RuntimeError(
            f"FunctionalAnalysis factorization proofs: expected 2 matches, found {text.count(old)}"
        )
    text = text.replace(old, """  rw [mixedDerivative_comm hf z, sub_self, mul_zero, add_zero] at h
  rw [h]
  ring
""", 1)
    text = text.replace(old, """  rw [mixedDerivative_comm hf z, sub_self, mul_zero, add_zero] at h
  exact h.symm
""", 1)
    print("FunctionalAnalysis orient both factorization identities directly: applied 2")
    old_cod = "Submodule.codRestrict realSmoothSubmodule"
    if text.count(old_cod) != 3:
        raise RuntimeError(
            f"FunctionalAnalysis linear-map codRestrict API: expected 3 matches, found {text.count(old_cod)}"
        )
    text = text.replace(old_cod, "LinearMap.codRestrict realSmoothSubmodule")
    print("FunctionalAnalysis use LinearMap.codRestrict for all smooth operators: applied 3")
    path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
