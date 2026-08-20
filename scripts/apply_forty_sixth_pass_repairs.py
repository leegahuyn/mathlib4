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


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    groups = [
        ("objectSchema", "objectSchemaRequirements"),
        ("t1t5", "t1t5Requirements"),
        ("spt", "sptRequirements"),
        ("kernel", "kernelRequirements"),
        ("exactCoefficient", "exactCoefficientRequirements"),
        ("pAdic", "pAdicRequirements"),
        ("entropyRepro", "entropyReproRequirements"),
        ("finalInstance", "finalInstanceRequirements"),
    ]

    for suffix, group in groups:
        old = f"""theorem sectionOf_{suffix}_at
    (r : AdvancedClaimsIIRequirement)
    (h : List.Mem r {group}) :
    sectionOf r = Section.{suffix} := by
  have hm := List.mem_map_of_mem sectionOf h
  simpa [{group}, sectionOf] using hm
"""
        new = f"""theorem sectionOf_{suffix}_at
    (r : AdvancedClaimsIIRequirement)
    (h : List.Mem r {group}) :
    sectionOf r = Section.{suffix} := by
  cases r <;> simp [{group}, sectionOf] at h ⊢
"""
        text, did = replace_once(
            text, old, new,
            f"Mock1Advanced prove sectionOf_{suffix} by constructor analysis")
        changed |= did

        old = f"""theorem {suffix}_mem_all
    (r : AdvancedClaimsIIRequirement)
    (h : List.Mem r {group}) :
    List.Mem r all := by
  exact (by decide : {group}.Subset all) h
"""
        new = f"""theorem {suffix}_mem_all
    (r : AdvancedClaimsIIRequirement)
    (h : List.Mem r {group}) :
    List.Mem r all := by
  cases r <;> simp [{group}, all] at h ⊢
"""
        text, did = replace_once(
            text, old, new,
            f"Mock1Advanced prove {suffix} inclusion by constructor analysis")
        changed |= did

    old = """theorem mem_all (r : AdvancedClaimsIIRequirement) :
    List.Mem r all := by
  cases r <;> decide
"""
    new = """theorem mem_all (r : AdvancedClaimsIIRequirement) :
    List.Mem r all := by
  cases r <;> simp [all]
"""
    text, did = replace_once(
        text, old, new,
        "Mock1Advanced prove complete requirement membership by simplification")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """    rw [powerShiftHom_intCast, hs]
    simp
""",
            """    rw [powerShiftHom_intCast, hs, pow_zero, one_mul]
""",
            "Mock2 close the zero-shift surjectivity branch explicitly",
        ),
        (
            """  rw [powerShiftKernelHom_intCast,
    Tor1Canonical.gcdToKernelHom_intCast,
    generic_quotientStep_eq_pow_shift M p k hM hp]
""",
            """  rw [powerShiftKernelHom_intCast,
    Tor1Canonical.gcdToKernelHom_intCast,
    generic_quotientStep_eq_pow_shift M p k hM hp,
    Nat.cast_pow]
""",
            "Mock2 normalize the power cast in canonical kernel-map agreement",
        ),
        (
            """    have hx := congrArg φ x.2
    simpa only [map_mul, map_natCast, map_zero, PkReduction] using hx⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (PkReduction p k k' hkk)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (PkReduction p k k' hkk) x y
""",
            """    have hx := congrArg φ x.2
    change φ ((M : ZMod (Pk p k)) * x.1) = φ 0 at hx
    simpa only [map_mul, map_natCast, map_zero] using hx⟩
  map_zero' := by
    apply Subtype.ext
    change PkReduction p k k' hkk 0 = 0
    exact map_zero (PkReduction p k k' hkk)
  map_add' x y := by
    apply Subtype.ext
    change PkReduction p k k' hkk (x.1 + y.1) =
      PkReduction p k k' hkk x.1 + PkReduction p k k' hkk y.1
    exact map_add (PkReduction p k k' hkk) x.1 y.1
""",
            "Mock2 transport kernel membership and map laws through PkReduction",
        ),
        (
            """theorem shiftExponent_mono_of_le_k
    (M p : ℕ) {k' k : ℕ} (hkk : k' ≤ k) :
    shiftExponent M p k' ≤ shiftExponent M p k := by
  by_cases hv : valuationExponent M p ≤ k'
  · have hv' : valuationExponent M p ≤ k := hv.trans hkk
    unfold shiftExponent thicknessExponent
    rw [min_eq_left hv, min_eq_left hv']
    exact Nat.sub_le_sub_right hkk (valuationExponent M p)
  · have hkv : k' ≤ valuationExponent M p := le_of_not_ge hv
    have hz : shiftExponent M p k' = 0 := by
      unfold shiftExponent thicknessExponent
      rw [min_eq_right hkv, Nat.sub_self]
    rw [hz]
    exact Nat.zero_le _
""",
            """theorem shiftExponent_mono_of_le_k
    (M p : ℕ) {k' k : ℕ} (hkk : k' ≤ k) :
    shiftExponent M p k' ≤ shiftExponent M p k := by
  change k' - min (padicValNat p M) k' ≤
    k - min (padicValNat p M) k
  by_cases hv : padicValNat p M ≤ k'
  · have hv' : padicValNat p M ≤ k := hv.trans hkk
    rw [min_eq_left hv, min_eq_left hv']
    exact Nat.sub_le_sub_right hkk (padicValNat p M)
  · have hkv : k' ≤ padicValNat p M := le_of_not_ge hv
    rw [min_eq_right hkv, Nat.sub_self]
    exact Nat.zero_le _
""",
            "Mock2 prove shift-exponent monotonicity at the unfolded scalar level",
        ),
        (
            """  ext x
  apply (powerShiftEquiv M p k' hM hp).injective
  have h₁ := hsquare x
  have h₂ := rightNaturalitySquare M p hkk hM hp x
  simpa using h₁.symm.trans h₂
""",
            """  ext x
  apply powerShiftKernelHom_injective M p k' hM hp
  exact (hsquare x).symm.trans
    (rightNaturalitySquare M p hkk hM hp x)
""",
            "Mock2 use the kernel hom directly in right-map uniqueness",
        ),
        (
            """  simpa [leftThicknessMap] using
    ((powerShiftEquiv M' p k hM' hp).apply_symm_apply
      (leftKernelMap hMM p k (powerShiftKernelHom M p k hM hp x))).symm
""",
            """  change
    leftKernelMap hMM p k (powerShiftKernelHom M p k hM hp x) =
      (powerShiftEquiv M' p k hM' hp)
        ((powerShiftEquiv M' p k hM' hp).symm
          (leftKernelMap hMM p k
            (powerShiftKernelHom M p k hM hp x)))
  exact ((powerShiftEquiv M' p k hM' hp).apply_symm_apply
    (leftKernelMap hMM p k
      (powerShiftKernelHom M p k hM hp x))).symm
""",
            "Mock2 expose the equivalence in the left naturality square",
        ),
        (
            """  ext x
  apply (powerShiftEquiv M' p k hM' hp).injective
  have h₁ := hsquare x
  have h₂ := leftNaturalitySquare hMM p k hM hM' hp x
  simpa using h₁.symm.trans h₂
""",
            """  ext x
  apply powerShiftKernelHom_injective M' p k hM' hp
  exact (hsquare x).symm.trans
    (leftNaturalitySquare hMM p k hM hM' hp x)
""",
            "Mock2 use the kernel hom directly in left-map uniqueness",
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
            """  have hstar :
      (starRingEnd ℂ) ((starRingEnd ℂ) (J.factor γ τ : ℂ)) =
        (J.factor γ τ : ℂ) := star_star _
  rw [hstar]
""",
            """  simp only [star_star]
""",
            "Mock2Advanced simplify the double star under inversion",
        ),
        (
            """  have hcomp :
      pushFunction chart.coord.toEquiv u ∘
          (⇑chart.coord.toMeasurableEquiv) = u := by
    funext x
    exact Equiv.symm_apply_apply chart.coord.toEquiv x
""",
            """  have hcomp :
      pushFunction chart.coord.toEquiv u ∘
          (⇑chart.coord.toMeasurableEquiv) = u := by
    funext x
    simp [pushFunction]
""",
            "Mock2Advanced unfold the chart push-function composition",
        ),
    ]

    for old, new, label in replacements:
        count = text.count(old)
        if label == "Mock2Advanced unfold the chart push-function composition":
            if count == 2:
                text = text.replace(old, new)
                changed = True
                print(f"{label}: applied 2")
                continue
            if count == 0 and text.count(new) >= 2:
                print(f"{label}: already applied")
                continue
            raise RuntimeError(f"{label}: expected two matches, found {count}")
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  have hxTendsto : Filter.Tendsto (fun n ↦ (x (ψ n) : X)) Filter.atTop (nhds y) := by
    have hSum := (hDefectTendsto.comp hψ.tendsto_atTop).add hKy
    change Filter.Tendsto
      (fun n => ((x (ψ n) : X) - K (x (ψ n) : X)) +
        K (x (ψ n) : X)) Filter.atTop (nhds y) at hSum
    simpa only [sub_add_cancel] using hSum
""",
            """  have hxTendsto : Filter.Tendsto (fun n ↦ (x (ψ n) : X)) Filter.atTop (nhds y) := by
    have hSum := (hDefectTendsto.comp hψ.tendsto_atTop).add hKy
    change Filter.Tendsto
      (fun n => R (x (ψ n)) + ySeq (ψ n))
      Filter.atTop (nhds (0 + y)) at hSum
    have hfun :
        (fun n => R (x (ψ n)) + ySeq (ψ n)) =
          (fun n => (x (ψ n) : X)) := by
      funext n
      simp only [R, ySeq,
        fredholmDefectKernelComplementRestriction_apply,
        fredholmDefect_apply, sub_add_cancel]
    rw [hfun] at hSum
    simpa only [zero_add] using hSum
""",
            "FunctionalAnalysis identify the defect-plus-compact subsequence pointwise",
        ),
        (
            """theorem discretePotential_bounded_on_initialSegment (N : ℕ) :
    ∀ n ≤ N, discretePotential n ≤ discretePotential N := by
  intro n hn
  exact_mod_cast hn
""",
            """theorem discretePotential_bounded_on_initialSegment (N : ℕ) :
    ∀ n ≤ N, discretePotential n ≤ discretePotential N := by
  intro n hn
  change (n : ℝ) ≤ (N : ℝ)
  exact_mod_cast hn
""",
            "FunctionalAnalysis expose the real casts in the discrete potential bound",
        ),
        (
            """  have hbound : (n : ℝ) ≤ C := by
    simpa [discretePotentialForm, discretePotential,
      abs_of_nonneg (Nat.cast_nonneg n)] using hC n 1 1
""",
            """  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hbound : (n : ℝ) ≤ C := by
    simpa [discretePotentialForm, discretePotential,
      abs_of_nonneg hn0] using hC n 1 1
""",
            "FunctionalAnalysis type the nonnegative real cast in the form obstruction",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
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
