from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
input_sha = hashlib.sha256(text.encode()).hexdigest()
repairs = 0


def replace_once(old: str, new: str, label: str) -> None:
    global text, repairs
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'{label}: expected once, found {count}')
    text = text.replace(old, new)
    repairs += 1


# Align the proof-local measurable-space instance with the one carried by the
# selected restricted Lebesgue measure.
replace_once(
"""    MemLp (selectedCuspRestrictionRepresentative n q Y u) 2
      selectedHorocycleParameterMeasure := by
  let f := selectedCuspRestrictionRepresentative n q Y u
""",
"""    MemLp (selectedCuspRestrictionRepresentative n q Y u) 2
      selectedHorocycleParameterMeasure := by
  letI : MeasurableSpace ℝ := Real.measureSpace.toMeasurableSpace
  let f := selectedCuspRestrictionRepresentative n q Y u
""",
    '33675 measurable-space alignment',
)

# Normalize the associative/commutative scalar products produced by the
# product-rule theorem.
replace_once(
"""  have hprod := (hasDerivAt_id y).mul hnorm
  simpa only [one_mul] using hprod.deriv
""",
"""  have hprod := (hasDerivAt_id y).mul hnorm
  convert hprod.deriv using 1 <;> ring
""",
    '33891 product derivative normalization',
)

replace_once(
"""    |‖f y‖ ^ 2 + 2 * y * ⟪f y, deriv f y⟫_ℝ| ≤
        |‖f y‖ ^ 2| + |2 * y * ⟪f y, deriv f y⟫_ℝ| :=
      abs_add _ _
""",
"""    |‖f y‖ ^ 2 + 2 * y * ⟪f y, deriv f y⟫_ℝ| ≤
        |‖f y‖ ^ 2| + |2 * y * ⟪f y, deriv f y⟫_ℝ| :=
      abs_add_le _ _
""",
    '33907 renamed absolute-value triangle inequality',
)

replace_once(
"""        (mul_le_mul_of_nonneg_left hinner
          (mul_nonneg (by norm_num) hy)) _
""",
"""        (mul_le_mul_of_nonneg_left hinner (by positivity)) _
""",
    '33915 explicit nonnegative multiplier',
)

# Pointwise multiplication is not the to_additive companion of compact
# multiplicative support.  Prove the needed support inclusions directly.
replace_once(
"""  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    simpa only [pow_two] using hcompact.norm.mul hcompact.norm
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    simpa only [pow_two] using
      hcompact.deriv.norm.mul hcompact.deriv.norm
  have hweightedCompact : HasCompactSupport weighted := by
    simpa only [weighted, Pi.mul_apply] using
      hnormSq.mul_left (f := fun y : ℝ => y)
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    simpa only [Pi.mul_apply] using
      hnormSq.mul_left (f := fun _y : ℝ => (2 : ℝ))
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    simpa only [Pi.mul_apply] using
      hderivNormSq.mul_left (f := fun y : ℝ => y ^ 2)
""",
"""  have hnormSq : HasCompactSupport (fun y : ℝ => ‖f y‖ ^ 2) := by
    simpa only [Function.comp_apply] using
      hcompact.norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hderivNormSq :
      HasCompactSupport (fun y : ℝ => ‖deriv f y‖ ^ 2) := by
    simpa only [Function.comp_apply] using
      hcompact.deriv.norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hweightedCompact : HasCompactSupport weighted := by
    apply hnormSq.mono
    intro y hy hzero
    apply hy
    simp only [weighted, hzero, mul_zero]
  have hfirstCompact :
      HasCompactSupport (fun y : ℝ => 2 * ‖f y‖ ^ 2) := by
    apply hnormSq.mono
    intro y hy hzero
    apply hy
    simp only [hzero, mul_zero]
  have hsecondCompact :
      HasCompactSupport (fun y : ℝ => y ^ 2 * ‖deriv f y‖ ^ 2) := by
    apply hderivNormSq.mono
    intro y hy hzero
    apply hy
    simp only [hzero, mul_zero]
""",
    '33932-33946 compact-support construction',
)

replace_once(
"""    exact norm_deriv_height_mul_normSq_le
      (hf.differentiable (by norm_num)) (le_of_lt hy)
""",
"""    exact norm_deriv_height_mul_normSq_le
      (hf.differentiable (by norm_num))
      ((zero_le_one.trans hH).trans (le_of_lt hy))
""",
    '33979 positive tail height',
)

replace_once(
"""    H * ‖f H‖ ^ 2 = ‖weighted H‖ := by
      simp only [weighted, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hH0, abs_of_nonneg (sq_nonneg _)]
""",
"""    H * ‖f H‖ ^ 2 = ‖weighted H‖ := by
      rw [show weighted H = H * ‖f H‖ ^ 2 by rfl,
        Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hH0 (sq_nonneg _))]
""",
    '33982 norm of nonnegative weighted value',
)

replace_once(
"""    exact norm_deriv_normSq_le_energy
      (hf.differentiable (by norm_num)) r
""",
"""    have hpoint := norm_deriv_normSq_le_energy
      (hf.differentiable (by norm_num)) r
    simpa only [g, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))] using hpoint
""",
    '34048 nested real norms',
)

replace_once(
"""    ‖f r₀‖ ^ 2 = ‖g r₀‖ := by
      simp only [g, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
""",
"""    ‖f r₀‖ ^ 2 = ‖g r₀‖ := by
      rw [show g r₀ = ‖f r₀‖ ^ 2 by rfl,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
""",
    '34065 norm of squared norm',
)

path.write_text(text, encoding='utf-8')
print('input_sha256=' + input_sha)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('repairs=' + str(repairs))
