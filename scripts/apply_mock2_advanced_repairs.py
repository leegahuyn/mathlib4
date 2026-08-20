from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock2_Advanced.lean")


def rep(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    n = text.count(old)
    if n == 0:
        print(f"{label}: already applied/source changed")
        return text, False
    print(f"{label}: applied {n}")
    return text.replace(old, new), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False
    pairs = [
      ("↑((1 / ⟨z.im, z.im_pos.le⟩ : ℝ≥0) ^ 2)",
       "↑((1 / (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) ^ 2)", "NNReal density parentheses"),
      ("""theorem gamma2Act_measurePreserving (γ : Gamma2Element) :
    MeasurePreserving (gamma2Act γ) hyperbolicMeasure hyperbolicMeasure := by
  simpa only [hyperbolicMeasure, gamma2Act,
    MulAction.compHom_smul_def] using
    (measurePreserving_smul
      ((Matrix.SpecialLinearGroup.mapGL
        (n := Fin 2) (R := ℤ) ℝ)
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (volume : Measure UpperHalfPlane))
""",
"""theorem gamma2Act_measurePreserving (γ : Gamma2Element) :
    MeasurePreserving (gamma2Act γ) hyperbolicMeasure hyperbolicMeasure := by
  change MeasurePreserving
    (fun τ : UpperHalfPlane =>
      ((Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ)
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) • τ)
    (volume : Measure UpperHalfPlane) (volume : Measure UpperHalfPlane)
  exact measurePreserving_smul
    ((Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ)
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (volume : Measure UpperHalfPlane)
""", "measure preserving action"),
      ("""  ring

/-- The positive Gaussian tail is summable""",
"""  change
    -(Real.pi * (n : ℝ) * τ.im * 2) - Real.pi * (n : ℝ) ^ 2 * τ.im - Real.pi * τ.im =
      -(Real.pi * (n : ℝ) * τ.im * 2) - Real.pi * (n : ℝ) ^ 2 * τ.im - Real.pi * τ.im
  rfl

/-- The positive Gaussian tail is summable""", "theta coe-im normalization"),
      ("""  have hInt : IntegrableOn (gaussianMajorant y) (Set.Ioi (0 : ℝ)) := by
    simpa only [gaussianMajorant] using
      (integrableOn_Ioi_exp_neg_mul_sq_iff.mpr
        (mul_pos Real.pi_pos hy))
""",
"""  have hInt : IntegrableOn (gaussianMajorant y) (Set.Ioi (0 : ℝ)) := by
    change IntegrableOn (fun x : ℝ => Real.exp (-(Real.pi * y) * x ^ 2)) (Set.Ioi 0)
    exact integrableOn_Ioi_exp_neg_mul_sq_iff.mpr (mul_pos Real.pi_pos hy)
""", "Gaussian integrability"),
      ("""    _ = Real.sqrt (Real.pi / (Real.pi * τ.im)) / 2 := by
      rw [gaussianMajorant, integral_gaussian_Ioi]
""",
"""    _ = Real.sqrt (Real.pi / (Real.pi * τ.im)) / 2 := by
      change (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(Real.pi * τ.im) * x ^ 2)) = _
      rw [integral_gaussian_Ioi]
""", "Gaussian half-line integral"),
      ("simp only [factor_mul, gamma2Act_mul, mul_assoc])",
       "simp only [factor_mul, matrix_mul, gamma2Act_mul, mul_assoc])", "metaplectic associativity"),
      ("simp only [matrix_mul, matrix_inv, inv_mul]", "simp [matrix_mul, matrix_inv]", "matrix inverse"),
      ("simp only [factor_mul, factor_inv, hact, inv_mul]", "simp [factor_mul, factor_inv, hact]", "factor inverse"),
      ("""      map_one' := by
        apply Gamma2Metaplectic.ext <;> simp
""",
"""      map_one' := by
        apply Gamma2Metaplectic.ext
        · rfl
        · funext τ
          rfl
""", "trivial lift identity")]
    for old, new, label in pairs:
        text, c = rep(text, old, new, label)
        changed |= c
    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
