from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  letI : Countable Gamma2Element :=
    (show Function.Injective (fun γ : Gamma2Element => γ.1.1) by
      intro γ δ h
      apply Subtype.ext
      apply Subtype.ext
      exact h).countable
""",
        """  let encodeMatrix : Matrix (Fin 2) (Fin 2) ℤ → ℤ × ℤ × ℤ × ℤ :=
    fun A => (A 0 0, A 0 1, A 1 0, A 1 1)
  have encodeMatrix_injective : Function.Injective encodeMatrix := by
    intro A B h
    ext i j
    fin_cases i <;> fin_cases j
    · exact congrArg (fun t => t.1) h
    · exact congrArg (fun t => t.2.1) h
    · exact congrArg (fun t => t.2.2.1) h
    · exact congrArg (fun t => t.2.2.2) h
  letI : Countable Gamma2Element :=
    Countable.of_injective
      (fun γ : Gamma2Element => encodeMatrix γ.1.1) (by
        intro γ δ h
        apply Subtype.ext
        apply Subtype.ext
        exact encodeMatrix_injective h)
""",
        "Mock2 Advanced encode Gamma2 matrices into a countable integer tuple",
    )
    m2a = replace_exact(
        m2a,
        """  have hd : Continuous (fun z : UpperHalfPlane =>
      (1 / ⟨z.im, z.im_pos.le⟩ : ℝ≥0) ^ 2) := by
    refine .pow (.div₀ continuous_const ?_ ?_) _
    · exact UpperHalfPlane.continuous_im.subtype_mk _
    · exact fun z => NNReal.ne_iff.mp z.im_ne_zero
  rw [IntegrableOn, hyperbolicMeasure_def,
    Measure.restrict_withDensity ModularGroup.isClosed_fd.measurableSet,
    integrable_withDensity_iff_integrable_smul hd.measurable]
  change IntegrableOn
    (fun τ : UpperHalfPlane =>
      ((1 / ⟨τ.im, τ.im_pos.le⟩ : ℝ≥0) ^ 2) •
        (1 + Real.sqrt τ.im))
""",
        """  have hd : Continuous (fun z : UpperHalfPlane =>
      (1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) := by
    refine .pow (.div₀ continuous_const ?_ ?_) _
    · exact UpperHalfPlane.continuous_im.subtype_mk _
    · exact fun z => NNReal.ne_iff.mp z.im_ne_zero
  rw [IntegrableOn, hyperbolicMeasure_def,
    MeasureTheory.restrict_withDensity ModularGroup.isClosed_fd.measurableSet,
    integrable_withDensity_iff_integrable_smul hd.measurable]
  change IntegrableOn
    (fun τ : UpperHalfPlane =>
      ((1 / NNReal.mk τ.im τ.im_pos.le : NNReal) ^ 2) •
        (1 + Real.sqrt τ.im))
""",
        "Mock2 Advanced use current withDensity restriction and NNReal syntax",
    )
    m2a = replace_exact(
        m2a,
        """  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (mul_nonneg (by norm_num)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _)))] using hbound
""",
        """  simpa only [Real.norm_eq_abs,
    abs_of_nonneg
      (sq_nonneg ‖positivePeterssonQuarter τ * ConcreteUnaryTheta.theta τ‖)]
    using hbound
""",
        "Mock2 Advanced remove the absolute value of the nonnegative square",
    )
    m2a = replace_exact(
        m2a,
        "(2 : ℝ≥0∞)",
        "2",
        "Mock2 Advanced infer ENNReal exponents from context",
        expected=12,
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
