from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  all_rows_certified := by
    intro row hrow
    simp only [referenceOLSRows, List.mem_cons, List.mem_singleton] at hrow
    rcases hrow with hα | hrest
    · subst row
      exact ⟨referenceAlphaOLSRow.table_number_at,
        referenceAlphaOLSRow.estimate_mem_at,
        referenceAlphaOLSRow.mode_diagnostic_at⟩
    rcases hrest with hβ | hrest
    · subst row
      exact ⟨referenceBetaOLSRow.table_number_at,
        referenceBetaOLSRow.estimate_mem_at,
        referenceBetaOLSRow.mode_diagnostic_at⟩
    rcases hrest with hγ | hrest
    · subst row
      exact ⟨referenceGammaOLSRow.table_number_at,
        referenceGammaOLSRow.estimate_mem_at,
        referenceGammaOLSRow.mode_diagnostic_at⟩
    rcases hrest with hc | hrss
    · subst row
      exact ⟨referenceCeffOLSRow.table_number_at,
        referenceCeffOLSRow.estimate_mem_at,
        referenceCeffOLSRow.mode_diagnostic_at⟩
    · subst row
      exact ⟨referenceRSSOLSRow.table_number_at,
        referenceRSSOLSRow.estimate_mem_at,
        referenceRSSOLSRow.mode_diagnostic_at⟩
"""
    new = """  all_rows_certified := by
    intro row hrow
    simp only [referenceOLSRows, List.mem_cons, List.mem_singleton] at hrow
    rcases hrow with hα | hrest
    · subst row
      exact ⟨referenceAlphaOLSRow.table_number_at,
        referenceAlphaOLSRow.estimate_mem_at,
        referenceAlphaOLSRow.mode_diagnostic_at⟩
    · rcases hrest with hβ | hrest
      · subst row
        exact ⟨referenceBetaOLSRow.table_number_at,
          referenceBetaOLSRow.estimate_mem_at,
          referenceBetaOLSRow.mode_diagnostic_at⟩
      · rcases hrest with hγ | hrest
        · subst row
          exact ⟨referenceGammaOLSRow.table_number_at,
            referenceGammaOLSRow.estimate_mem_at,
            referenceGammaOLSRow.mode_diagnostic_at⟩
        · rcases hrest with hc | hrss
          · subst row
            exact ⟨referenceCeffOLSRow.table_number_at,
              referenceCeffOLSRow.estimate_mem_at,
              referenceCeffOLSRow.mode_diagnostic_at⟩
          · subst row
            exact ⟨referenceRSSOLSRow.table_number_at,
              referenceRSSOLSRow.estimate_mem_at,
              referenceRSSOLSRow.mode_diagnostic_at⟩
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced restore all OLS disjunction branches")
    changed |= did

    old = """    have hp' : p = ((-1 : ℤ), (1 : ℚ)) := by
      simpa [referenceT1PolarProfile] using hp
"""
    new = """    have hp' : p = ((-1 : ℤ), (1 : ℚ)) := by
      simpa only [referenceT1PolarProfile, List.mem_singleton] using hp
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced reduce singleton polar-profile membership")
    changed |= did

    old = """    have hp' : p = ((-2 : ℤ), (1 : ℚ)) ∨
        p = ((-1 : ℤ), (1 : ℚ)) := by
      simpa [referenceT2PolarProfile] using hp
"""
    new = """    have hp' : p = ((-2 : ℤ), (1 : ℚ)) ∨
        p = ((-1 : ℤ), (1 : ℚ)) := by
      simpa only [referenceT2PolarProfile, List.mem_cons,
        List.mem_singleton] using hp
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced reduce two-row polar-profile membership")
    changed |= did

    text, did = replace_once(text,
        """theorem mem_all (r : BetaArchimedeanDRequirement) :
    List.Mem r all := by
  cases r <;> simp [all]
""",
        """theorem mem_all (r : BetaArchimedeanDRequirement) :
    List.Mem r all := by
  cases r <;> decide
""",
        "Mock1Advanced decide the seven closed beta-archimedean requirements")
    changed |= did

    text, did = replace_once(text,
        """theorem mem_all (r : ExactCoefficientERequirement) :
    List.Mem r all := by
  cases r <;> simp [all]
""",
        """theorem mem_all (r : ExactCoefficientERequirement) :
    List.Mem r all := by
  cases r <;> decide
""",
        "Mock1Advanced decide the twelve exact-coefficient requirements")
    changed |= did

    scalar_replacements = [
        ("  scalar_eq := rfl\n", "  scalar_eq := by norm_num\n",
         "Mock1Advanced normalize the reference archimedean scalar"),
        ("  normalizedValue_eq_rat := rfl\n", "  normalizedValue_eq_rat := by norm_num\n",
         "Mock1Advanced normalize the integral rational value"),
        ("  normalizedValue_eq_value := rfl\n", "  normalizedValue_eq_value := by norm_num\n",
         "Mock1Advanced normalize the value-bound certificate"),
        ("  scalar_formula := rfl\n", "  scalar_formula := by norm_num\n",
         "Mock1Advanced normalize the scalar formula input"),
    ]
    for old, new, label in scalar_replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem powerShiftIntegerHom_modulus_eq_zero (M p k : ℕ) :
    powerShiftIntegerHom M p k
      (p ^ thicknessExponent M p k : ℤ) = 0 := by
  rw [powerShiftIntegerHom_apply]
  rw [← Nat.cast_mul, pow_shift_mul_pow_thickness]
  exact ZMod.natCast_self (Pk p k)
"""
    new = """theorem powerShiftIntegerHom_modulus_eq_zero (M p k : ℕ) :
    powerShiftIntegerHom M p k
      (p ^ thicknessExponent M p k : ℤ) = 0 := by
  rw [powerShiftIntegerHom_apply]
  have h :
      ((p ^ shiftExponent M p k * p ^ thicknessExponent M p k : ℕ) :
        ZMod (Pk p k)) = 0 := by
    rw [pow_shift_mul_pow_thickness]
    exact ZMod.natCast_self (Pk p k)
  simpa only [Nat.cast_mul, Nat.cast_pow, Int.cast_natCast] using h
"""
    text, did = replace_once(text, old, new,
        "Mock2 prove the power-shift modulus through an explicit natural cast")
    changed |= did

    old = """@[simp] theorem powerShiftHom_intCast
    (M p k : ℕ) (z : ℤ) :
    powerShiftHom M p k
        (z : ZMod (p ^ thicknessExponent M p k)) =
      (p ^ shiftExponent M p k : ZMod (Pk p k)) *
        (z : ZMod (Pk p k)) := by
  change powerShiftIntegerHom M p k z = _
  exact powerShiftIntegerHom_apply M p k z
"""
    new = """@[simp] theorem powerShiftHom_intCast
    (M p k : ℕ) (z : ℤ) :
    powerShiftHom M p k
        (z : ZMod (p ^ thicknessExponent M p k)) =
      (p ^ shiftExponent M p k : ZMod (Pk p k)) *
        (z : ZMod (Pk p k)) := by
  simpa only [powerShiftHom] using powerShiftIntegerHom_apply M p k z
"""
    text, did = replace_once(text, old, new,
        "Mock2 expose ZMod.lift on integer representatives")
    changed |= did

    old = """  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [powerShiftHom_intCast, ← mul_assoc, ← Nat.cast_mul]
  have hzero :
      (M * p ^ shiftExponent M p k : ZMod (Pk p k)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2
      (Pk_dvd_M_mul_shift M p k hM hp)
  rw [hzero, zero_mul]
"""
    new = """  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [powerShiftHom_intCast, ← mul_assoc]
  have hzero :
      (M : ZMod (Pk p k)) *
        (p ^ shiftExponent M p k : ZMod (Pk p k)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      (show (M * p ^ shiftExponent M p k : ZMod (Pk p k)) = 0 from
        (ZMod.natCast_eq_zero_iff _ _).2
          (Pk_dvd_M_mul_shift M p k hM hp))
  rw [hzero, zero_mul]
"""
    text, did = replace_once(text, old, new,
        "Mock2 normalize the kernel condition before applying divisibility")
    changed |= did

    old = """  have hz' :
      ((((p ^ shiftExponent M p k : ℕ) : ℤ) * (a - b) : ℤ) :
        ZMod (Pk p k)) = 0 := by
    simpa using hz
"""
    new = """  have hz' :
      ((((p ^ shiftExponent M p k : ℕ) : ℤ) * (a - b) : ℤ) :
        ZMod (Pk p k)) = 0 := by
    simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow] using hz
"""
    text, did = replace_once(text, old, new,
        "Mock2 normalize the injectivity integer product cast")
    changed |= did

    text, did = replace_once(text,
        """    have hs : shiftExponent M p k = k - valuationExponent M p := by
      simp [shiftExponent, hm]
""",
        """    have hs : shiftExponent M p k = k - valuationExponent M p := by
      unfold shiftExponent
      rw [hm]
""",
        "Mock2 rewrite the positive-valuation shift definition directly")
    changed |= did

    text, did = replace_once(text,
        """    have hs : shiftExponent M p k = 0 := by
      simp [shiftExponent, hm]
""",
        """    have hs : shiftExponent M p k = 0 := by
      unfold shiftExponent
      rw [hm]
      exact Nat.sub_self k
""",
        "Mock2 rewrite the saturated shift definition directly")
    changed |= did

    old = """    have hpz' :
        ((((p ^ valuationExponent M p : ℕ) : ℤ) * z : ℤ) :
          ZMod (Pk p k)) = 0 := by
      simpa using hpz
"""
    new = """    have hpz' :
        ((((p ^ valuationExponent M p : ℕ) : ℤ) * z : ℤ) :
          ZMod (Pk p k)) = 0 := by
      simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow] using hpz
"""
    text, did = replace_once(text, old, new,
        "Mock2 normalize the surjectivity integer product cast")
    changed |= did

    text, did = replace_once(text,
        """  apply Nat.mul_right_cancel
    (Nat.pow_pos hp.pos (thicknessExponent M p k))
  calc
""",
        """  apply Nat.mul_right_cancel
  calc
""",
        "Mock2 use Nat.mul_right_cancel with its current signature")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ↑((1 / (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) ^ 2) :=
  UpperHalfPlane.volume_def
"""
    new = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ENNReal.ofNNReal ((1 / NNReal.mk z.im z.im_pos.le) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    text, changed = replace_once(text, old, new,
        "Mock2Advanced give the hyperbolic density an explicit ENNReal codomain")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
