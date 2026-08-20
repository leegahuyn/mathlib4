from __future__ import annotations

from pathlib import Path

import apply_one_hundred_nineteenth_pass_repairs as pass119
import apply_one_hundred_twentieth_pass_repairs as pass120
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


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  rw [← normalizedFourier_eq_mathlib
    (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) ξ]
  calc
    normalizedFourier
          (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) ξ =
        (smoothTentAutocorrelationScale T hT : ℂ) *
          normalizedFourier
            (fun x : ℝ => (smoothTentAutocorrelationRaw T hT x : ℂ)) ξ := by
      simp only [normalizedFourier, fourierPositiveSmoothTentFunction,
        Complex.ofReal_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ((smoothTentAutocorrelationScale T hT *
          Complex.normSq
            (𝓕 (fun x : ℝ => (narrowSmoothTentFunction T hT x : ℂ)) ξ) : ℝ) : ℂ) := by
      rw [normalizedFourier_eq_mathlib,
        fourier_smoothTentAutocorrelationRaw_eq_normSq T hT ξ,
        Complex.ofReal_mul]
""",
            """  rw [← TentKernel.normalizedFourier_eq_mathlib
    (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) ξ]
  calc
    TentKernel.normalizedFourier
          (fun x : ℝ => (fourierPositiveSmoothTentFunction T hT x : ℂ)) ξ =
        (smoothTentAutocorrelationScale T hT : ℂ) *
          TentKernel.normalizedFourier
            (fun x : ℝ => (smoothTentAutocorrelationRaw T hT x : ℂ)) ξ := by
      simp only [TentKernel.normalizedFourier, fourierPositiveSmoothTentFunction,
        Complex.ofReal_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ((smoothTentAutocorrelationScale T hT *
          Complex.normSq
            (𝓕 (fun x : ℝ => (narrowSmoothTentFunction T hT x : ℂ)) ξ) : ℝ) : ℂ) := by
      rw [TentKernel.normalizedFourier_eq_mathlib,
        fourier_smoothTentAutocorrelationRaw_eq_normSq T hT ξ,
        Complex.ofReal_mul]
""",
            1,
            "Mock2Advanced qualify the complete normalized Fourier calculation",
        ),
        (
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    change AEStronglyMeasurable
""",
            """  normalizedKernel_aestronglyMeasurable := by
    intro x hx
    simp only [profileBesselConvention, Convention.normalizedKernel, one_mul]
    change AEStronglyMeasurable
""",
            1,
            "Mock2Advanced unfold the concrete convention before changing the measurable kernel",
        ),
        (
            """  rw [hentry]
  apply (Int.natAbs_eq_iff_mul_self_eq).2
  calc
    (L 1 1 * G 1 0 * R 0 0) *
        (L 1 1 * G 1 0 * R 0 0) =
        (L 1 1 * L 1 1) * (G 1 0 * G 1 0) *
          (R 0 0 * R 0 0) := by ring
    _ = G 1 0 * G 1 0 := by rw [hLsq, hRsq]; ring
""",
            """  rw [hentry, Int.natAbs_mul, Int.natAbs_mul]
  have hnatLsq : Int.natAbs (L 1 1) * Int.natAbs (L 1 1) = 1 := by
    simpa only [Int.natAbs_mul, Int.natAbs_one] using congrArg Int.natAbs hLsq
  have hnatRsq : Int.natAbs (R 0 0) * Int.natAbs (R 0 0) = 1 := by
    simpa only [Int.natAbs_mul, Int.natAbs_one] using congrArg Int.natAbs hRsq
  have hnatL : Int.natAbs (L 1 1) = 1 := by omega
  have hnatR : Int.natAbs (R 0 0) = 1 := by omega
  simp [hnatL, hnatR]
""",
            1,
            "Mock2Advanced prove lower-left natAbs invariance through multiplicativity",
        ),
        (
            """  sum_integral_interchange (B.integrable m)
    (B.summable_integral_norm m)
""",
            """  Mock2Adv.Interchange.sum_integral_interchange (B.integrable m)
    (B.summable_integral_norm m)
""",
            1,
            "Mock2Advanced call the ambient Tonelli certificate rather than the method recursively",
        ),
        (
            """  exact integrable_dirac (by simp [kernel])
""",
            """  exact integrable_dirac (by positivity)
""",
            1,
            "Mock2Advanced prove positivity of the geometric denominator directly",
        ),
        (
            """  filter_upwards [hlt, eventually_ge_atTop m₀] with m hm_lt hm_ge
  exact (not_lt_of_ge (hlower m hm_ge)) hm_lt
""",
            """  have hex : ∃ m, massFunctional D m < ε ∧ m₀ ≤ m :=
    (hlt.and (eventually_ge_atTop m₀)).exists
  rcases hex with ⟨m, hm_lt, hm_ge⟩
  exact (not_lt_of_ge (hlower m hm_ge)) hm_lt
""",
            1,
            "Mock2Advanced extract one large index from the eventual contradiction",
        ),
        (
            """  activeSet_finite : volume activeSet ≠ (⊤ : ℝ≥0∞)
""",
            """  activeSet_finite : volume activeSet ≠ (⊤ : ENNReal)
""",
            1,
            "Mock2Advanced avoid parser ambiguity in the active-set finite-measure field",
        ),
    ])


def main() -> int:
    pass119.main()
    pass120.repair_mock1_advanced()
    pass120.repair_mock2()
    repair_mock2_advanced()
    pass120.repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
