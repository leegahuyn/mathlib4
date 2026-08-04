from __future__ import annotations

import re
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

    replacements = [
        (
            """    have hEq :
        ("M 9.1.6 T/S residual table" : String) =
          "K.6 final statement Theorem K.2" := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
""",
            """    have hEq :
        ("M 9.1.6 T/S residual table" : String) =
          "K.6 final statement Theorem K.2" :=
      List.mem_singleton.mp h
""",
            "Mock1Advanced extract residual-table equality from singleton membership",
        ),
        (
            """    have hEq : T = referenceTransportedPrincipalPart := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hT
""",
            """    have hEq : T = referenceTransportedPrincipalPart :=
      List.mem_singleton.mp hT
""",
            "Mock1Advanced extract transported row equality from singleton membership",
        ),
        (
            """theorem mem_all (r : AdvancedClaimsIIRequirement) :
    List.Mem r all := by
  cases r <;> simp [all]
""",
            """theorem mem_all (r : AdvancedClaimsIIRequirement) :
    List.Mem r all := by
  cases r <;> decide
""",
            "Mock1Advanced decide the complete stage-II requirement registry",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    groups = [
        ("objectSchema", "objectSchemaRequirements", "Section.objectSchema"),
        ("t1t5", "t1t5Requirements", "Section.t1t5"),
        ("spt", "sptRequirements", "Section.spt"),
        ("kernel", "kernelRequirements", "Section.kernel"),
        ("exactCoefficient", "exactCoefficientRequirements", "Section.exactCoefficient"),
        ("pAdic", "pAdicRequirements", "Section.pAdic"),
        ("entropyRepro", "entropyReproRequirements", "Section.entropyRepro"),
        ("finalInstance", "finalInstanceRequirements", "Section.finalInstance"),
    ]
    for suffix, group, section in groups:
        start = f"""theorem sectionOf_{suffix}_at
    (r : AdvancedClaimsIIRequirement)
    (h : List.Mem r {group}) :
    sectionOf r = {section} := by
"""
        pattern = re.compile(
            re.escape(start) + r"(?:  .*\n)+?(?=\ntheorem )",
            flags=re.MULTILINE,
        )
        match = pattern.search(text)
        new_block = start + f"""  have hm := List.mem_map_of_mem sectionOf h
  simpa [{group}, sectionOf] using hm
"""
        if match:
            text = text[:match.start()] + new_block + text[match.end():]
            changed = True
            print(f"Mock1Advanced prove sectionOf_{suffix} through mapped membership: applied")
        elif new_block in text:
            print(f"Mock1Advanced prove sectionOf_{suffix} through mapped membership: already applied")
        else:
            raise RuntimeError(f"Mock1Advanced sectionOf_{suffix} block not found")

        mem_start = f"""theorem {suffix}_mem_all
    (r : AdvancedClaimsIIRequirement)
    (h : List.Mem r {group}) :
    List.Mem r all := by
"""
        mem_pattern = re.compile(
            re.escape(mem_start) + r"(?:  .*\n)+?(?=\ntheorem )",
            flags=re.MULTILINE,
        )
        mem_match = mem_pattern.search(text)
        mem_new = mem_start + f"""  exact (by decide : {group}.Subset all) h
"""
        if mem_match:
            text = text[:mem_match.start()] + mem_new + text[mem_match.end():]
            changed = True
            print(f"Mock1Advanced prove {suffix} inclusion by closed subset decision: applied")
        elif mem_new in text:
            print(f"Mock1Advanced prove {suffix} inclusion by closed subset decision: already applied")
        else:
            raise RuntimeError(f"Mock1Advanced {suffix}_mem_all block not found")

    qualified, n_tendsto = re.subn(r"(?<![\w.])Tendsto\b", "Filter.Tendsto", text)
    qualified, n_attop = re.subn(r"(?<![\w.])atTop\b", "Filter.atTop", qualified)
    if n_tendsto or n_attop:
        print(f"Mock1Advanced qualify Filter names: Tendsto={n_tendsto}, atTop={n_attop}")
        text = qualified
        changed = True

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """    simpa only [Int.cast_mul, Int.cast_natCast,
      Nat.cast_pow] using hz
""",
            """    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Nat.cast_pow] using hz
""",
            "Mock2 normalize both integer and natural power casts in injectivity",
        ),
        (
            """      simpa only [Int.cast_mul, Int.cast_natCast,
        Nat.cast_pow] using hpz
""",
            """      simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
        Nat.cast_pow] using hpz
""",
            "Mock2 normalize both integer and natural power casts in surjectivity",
        ),
        (
            """    simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow] using hqcast
""",
            """    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Nat.cast_pow] using hqcast
""",
            "Mock2 normalize quotient representative power casts",
        ),
        (
            """    rw [powerShiftHom_intCast]
    simp [shiftExponent, hm]
""",
            """    rw [powerShiftHom_intCast, hs]
    simp
""",
            "Mock2 use the established zero shift in the saturated branch",
        ),
        (
            """  apply Subtype.ext
  change
    (p ^ shiftExponent M p k : ZMod (Pk p k)) *
        (z : ZMod (Pk p k)) =
      (Tor1Canonical.quotientStep M (Pk p k) : ZMod (Pk p k)) *
        (z : ZMod (Pk p k))
  rw [generic_quotientStep_eq_pow_shift M p k hM hp]
""",
            """  apply Subtype.ext
  rw [powerShiftKernelHom_intCast,
    Tor1Canonical.gcdToKernelHom_intCast,
    generic_quotientStep_eq_pow_shift M p k hM hp]
""",
            "Mock2 compare canonical kernel maps through their integer-cast lemmas",
        ),
        (
            """  map_zero' := by
    apply Subtype.ext
    simp [PkReduction]
  map_add' x y := by
    apply Subtype.ext
    simp [PkReduction]
""",
            """  map_zero' := by
    apply Subtype.ext
    exact map_zero (PkReduction p k k' hkk)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (PkReduction p k k' hkk) x y
""",
            "Mock2 prove right-kernel map laws through the bundled reduction hom",
        ),
        (
            """  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp [mul_add]
""",
            """  map_zero' := by
    apply Subtype.ext
    change (M / M' : ZMod (Pk p k)) * 0 = 0
    exact mul_zero _
  map_add' x y := by
    apply Subtype.ext
    change
      (M / M' : ZMod (Pk p k)) * (x.1 + y.1) =
        (M / M' : ZMod (Pk p k)) * x.1 +
          (M / M' : ZMod (Pk p k)) * y.1
    exact mul_add _ _ _
""",
            "Mock2 prove left-kernel map laws on underlying values",
        ),
        (
            """  by_cases hv : valuationExponent M p ≤ k'
  · have hv' : valuationExponent M p ≤ k := hv.trans hkk
    simpa [shiftExponent, thicknessExponent, min_eq_left hv,
      min_eq_left hv'] using
        (Nat.sub_le_sub_right hkk (valuationExponent M p))
  · have hkv : k' ≤ valuationExponent M p := le_of_not_ge hv
    have hz : shiftExponent M p k' = 0 := by
      simp [shiftExponent, thicknessExponent, min_eq_right hkv]
    rw [hz]
    exact Nat.zero_le _
""",
            """  by_cases hv : valuationExponent M p ≤ k'
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
            "Mock2 prove shift monotonicity by explicit minimum branches",
        ),
        (
            """  simp [rightThicknessMap]
""",
            """  change
    (p ^ (shiftExponent M p k - shiftExponent M p k') :
        ZMod (p ^ thicknessExponent M p k')) *
      (ZMod.castHom
        (pow_dvd_pow p (thicknessExponent_mono_of_le_k M p hkk))
        (ZMod (p ^ thicknessExponent M p k'))
        (z : ZMod (p ^ thicknessExponent M p k))) = _
  rw [map_intCast]
""",
            "Mock2 evaluate the right-thickness map on integer representatives",
        ),
        (
            """  simpa using rightThicknessMap_intCast M p hkk z
""",
            """  rw [rightThicknessMap_intCast]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_pow]
""",
            "Mock2 normalize the integer-cast form of the right-thickness map",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    old = """  toFun x := ⟨PkReduction p k k' hkk x.1, by
    apply (Tor1CyclicModel_mem_iff M (Pk p k') _).2
    have hx := congrArg
      (ZMod.castHom (by simpa [Pk] using pow_dvd_pow p hkk)
        (ZMod (Pk p k'))) x.2
    simpa [PkReduction] using hx⟩
"""
    new = """  toFun x := ⟨PkReduction p k k' hkk x.1, by
    apply (Tor1CyclicModel_mem_iff M (Pk p k') _).2
    let φ := ZMod.castHom (by simpa [Pk] using pow_dvd_pow p hkk)
      (ZMod (Pk p k'))
    have hx := congrArg φ x.2
    simpa only [map_mul, map_natCast, map_zero, PkReduction] using hx⟩
"""
    text, did = replace_once(
        text, old, new,
        "Mock2 transport kernel membership through the prime-power ring hom")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀, star_star]
""",
            """  rw [hu γ τ, hv γ τ, map_mul, map_inv₀]
  have hstar :
      (starRingEnd ℂ) ((starRingEnd ℂ) (J.factor γ τ : ℂ)) =
        (J.factor γ τ : ℂ) := star_star _
  rw [hstar]
""",
            "Mock2Advanced cancel the double star with an explicitly typed equality",
        ),
        (
            """  simpa only [pushFunction, Function.comp_apply, Equiv.symm_apply_apply] using
    (chart.coord.toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure
      (μ := μ) (g := pushFunction chart.coord.toEquiv u) (p := p))
""",
            """  have h :=
    chart.coord.toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure
      (μ := μ) (g := pushFunction chart.coord.toEquiv u) (p := p)
  have hcomp :
      pushFunction chart.coord.toEquiv u ∘
          (⇑chart.coord.toMeasurableEquiv) = u := by
    funext x
    exact Equiv.symm_apply_apply chart.coord.toEquiv x
  simpa only [hcomp] using h
""",
            "Mock2Advanced identify the chart push-pull composition in eLpNorm",
        ),
        (
            """  simpa only [pushFunction, Function.comp_apply, Equiv.symm_apply_apply] using
    (chart.coord.toMeasurableEquiv.memLp_map_measure_iff
      (μ := μ) (g := pushFunction chart.coord.toEquiv u) (p := p))
""",
            """  have h := chart.coord.toMeasurableEquiv.memLp_map_measure_iff
      (μ := μ) (g := pushFunction chart.coord.toEquiv u) (p := p)
  have hcomp :
      pushFunction chart.coord.toEquiv u ∘
          (⇑chart.coord.toMeasurableEquiv) = u := by
    funext x
    exact Equiv.symm_apply_apply chart.coord.toEquiv x
  simpa only [hcomp] using h
""",
            "Mock2Advanced identify the chart push-pull composition in MemLp",
        ),
        (
            """  have hz := congrArg (fun k : Z →ₗ[ℂ] A => k z) hg
  change (g z : A) = f z
  simpa only [LinearMap.comp_apply] using hz
""",
            """  have hz := congrArg (fun k : Z →ₗ[ℂ] A => k z) hg
  change (g z : A) = f z at hz
  exact hz
""",
            "Mock2Advanced unfold the balanced-equalizer inclusion in the hypothesis",
        ),
    ]
    for old, new, label in replacements:
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
            """              rw [show (starRingEnd ℂ) (r : ℂ) = (r : ℂ) by
                simp [starRingEnd_apply, Complex.star_def]]
              exact Complex.re_ofReal_mul r (F v) }
""",
            """              rw [starRingEnd_apply, Complex.star_def,
                Complex.conj_ofReal]
              exact Complex.re_ofReal_mul r (F v) }
""",
            "FunctionalAnalysis rewrite conjugation of a real scalar without recursive simp",
        ),
        (
            """            rw [show (starRingEnd ℂ) (r : ℂ) = (r : ℂ) by
              simp [starRingEnd_apply, Complex.star_def]]
            exact Complex.re_ofReal_mul r (B u v))
""",
            """            rw [starRingEnd_apply, Complex.star_def,
              Complex.conj_ofReal]
            exact Complex.re_ofReal_mul r (B u v))
""",
            "FunctionalAnalysis rewrite form conjugation of a real scalar without recursive simp",
        ),
        (
            """    simpa only [Function.comp_apply, R,
      fredholmDefectKernelComplementRestriction_apply, ySeq,
      fredholmDefect_apply, sub_add_cancel, zero_add] using hSum
""",
            """    change Filter.Tendsto
      (fun n => ((x (ψ n) : X) - K (x (ψ n) : X)) +
        K (x (ψ n) : X)) Filter.atTop (nhds y) at hSum
    simpa only [sub_add_cancel] using hSum
""",
            "FunctionalAnalysis expose the pointwise defect-plus-compact identity",
        ),
        (
            """    have hSmall := hxTendsto c hc
    filter_upwards [hSmall] with n hn
    exact (not_lt_of_ge (by simpa using hxNormLower (ψ n))) hn
""",
            """    have hSmall := hxTendsto c hc
    obtain ⟨n, hn⟩ := hSmall.exists
    exact (not_lt_of_ge (by simpa using hxNormLower (ψ n))) hn
""",
            "FunctionalAnalysis extract one index from the eventual small-norm bound",
        ),
        (
            """  have hyZero : y = 0 := by
    apply inner_self_eq_zero.mp
""",
            """  have hyZero : y = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
""",
            "FunctionalAnalysis specify the scalar field in the compactness contradiction",
        ),
        (
            """  exact norm_nonneg _
""",
            """  exact norm_nonneg
    (d.canonicalSolutionOperator : A.range →L[ℂ] V)
""",
            "FunctionalAnalysis specify the operator type in canonical norm nonnegativity",
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
