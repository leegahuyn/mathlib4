import Mathlib

open scoped ComplexConjugate
open MeasureTheory Set

example {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    ‖(0 : H →L[ℂ] H)‖ = 0 := by
  simp

example (a b : ℝ) :
    (∫ (_t : ℝ) in Icc a b, (0 : ℂ)) = 0 := by
  simp

example (j y p : ℂ) (hj : j ≠ 0) :
    (y / (Complex.normSq j : ℂ)) ^ (2 : ℕ) *
        star (j ^ (2 : ℕ) * p) =
      j ^ (-2 : ℤ) * (y ^ (2 : ℕ) * star p) := by
  have hjc : star j ≠ 0 := by
    intro h
    apply hj
    have h' := congrArg star h
    simpa using h'
  have hstarMul :
      star (j ^ (2 : ℕ) * p) = star (j ^ (2 : ℕ)) * star p := by
    simpa only [starRingEnd_apply] using
      (map_mul (starRingEnd ℂ) (j ^ (2 : ℕ)) p)
  have hstarPow :
      star (j ^ (2 : ℕ)) = (star j) ^ (2 : ℕ) := by
    simpa only [starRingEnd_apply] using
      (map_pow (starRingEnd ℂ) j (2 : ℕ))
  rw [hstarMul, hstarPow]
  rw [show (Complex.normSq j : ℂ) = star j * j by
    exact Complex.normSq_eq_conj_mul_self]
  simp only [zpow_negSucc, zpow_ofNat]
  field_simp [hj, hjc]
  <;> ring
