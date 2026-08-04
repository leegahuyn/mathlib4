from __future__ import annotations

from pathlib import Path
import re

import apply_one_hundred_ninth_pass_repairs as pass109
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


def repair_mock1_advanced() -> None:
    apply_replacements(ROOT / "Mock1_Advanced.lean", [
        (
            """  cases hblock with
  | head => decide
  | tail _ hblock =>
      cases hblock with
      | head => decide
      | tail _ hblock =>
          cases hblock with
          | head => decide
          | tail _ hnil => cases hnil
""",
            """  cases hblock with
  | head => norm_num [referenceMock1MList, referenceMock1RPhases]
  | tail _ hblock =>
      cases hblock with
      | head => norm_num [referenceMock1MList, referenceMock1RPhases]
      | tail _ hblock =>
          cases hblock with
          | head => norm_num [referenceMock1MList, referenceMock1RPhases]
          | tail _ hnil => cases hnil
""",
            1,
            "Mock1Advanced prove all three weighted-block memberships directly",
        ),
        (
            """  have h1 := h (1 : Fin 6)
  have hw := advanced_claims_ii_ramanujan_f_padic_worked_table_witness
  rw [hw.1, hw.2] at h1
  norm_num at h1
""",
            """  have h1 := h (1 : Fin 6)
  change AdvancedClaimsIIRamanujanFPAdicResidueValue 1 =
    AdvancedClaimsIIPaperI2NormalizedValue 1 at h1
  have hw := advanced_claims_ii_ramanujan_f_padic_worked_table_witness
  rw [hw.1, hw.2] at h1
  norm_num at h1
""",
            1,
            "Mock1Advanced normalize the Fin-indexed worked-table equality",
        ),
        (
            """theorem evidenceClass_exhaustive (r : AdvancedClaimsIIRequirement) :
""",
            """set_option maxHeartbeats 800000 in
theorem evidenceClass_exhaustive (r : AdvancedClaimsIIRequirement) :
""",
            1,
            "Mock1Advanced localize heartbeats to the exhaustive requirement split",
        ),
    ])


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """theorem zero_convergesAt (q : ℂ) :
    (0 : QSeries).ConvergesAt q := by
  simpa [ConvergesAt, term] using
    (summable_zero : Summable (fun _ : ℕ => (0 : ℂ)))
""",
        """theorem zero_convergesAt (q : ℂ) :
    (0 : QSeries).ConvergesAt q := by
  change Summable (fun n : ℕ => (0 : ℂ) * q ^ n)
  simpa only [zero_mul] using
    (summable_zero : Summable (fun _ : ℕ => (0 : ℂ)))
""",
        1,
        "Mock2 prove zero-series convergence from the zero summable family",
    )
    changed |= did

    count = len(re.findall(r"\bmatches\b", text))
    escaped_count = text.count("«matches»")
    if count == 6:
        text = re.sub(r"\bmatches\b", "«matches»", text)
        changed = True
        print("Mock2 escape six reserved matches identifiers: applied 6")
    elif escaped_count == 6:
        print("Mock2 escape six reserved matches identifiers: already applied")
    else:
        raise RuntimeError(
            f"Mock2 matches identifier count unexpected: plain={count}, escaped={escaped_count}"
        )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """    simpa only [mul_one] using
      ((((hasDerivAt_id (x : ℂ)).const_mul B).comp_ofReal).const_add A)
""",
            """    convert
      ((((hasDerivAt_id (x : ℂ)).const_mul B).comp_ofReal).const_add A)
      using 1 <;> first | rfl | simp only [id_eq, mul_one]
""",
            1,
            "Mock2Advanced align the affine derivative across complex structures",
        ),
        (
            """    simpa only [mul_one] using
      ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
""",
            """    convert ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
      using 1 <;> first | rfl | simp only [id_eq, mul_one]
""",
            1,
            "Mock2Advanced align the exponential derivative across complex structures",
        ),
        (
            """  rw [hzero]
  simp
""",
            """  rw [hzero]
  exact Filter.eventually_bot
""",
            1,
            "Mock2Advanced prove equality almost everywhere for the zero measure",
        ),
        (
            """  rw [Convention.transform, Convention.transform]
  simp only [Convention.scaleNormalization_normalizedKernel,
    Convention.scaleNormalization]
  change
""",
            """  rw [Convention.transform, Convention.transform]
  simp_rw only [Convention.scaleNormalization_normalizedKernel]
  change
""",
            1,
            "Mock2Advanced rewrite the scaled normalized kernel before the integral",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    plain_count = text.count("ContDiff ℝ ∞")
    typed_count = text.count("ContDiff ℝ (∞ : ℕ∞)")
    if plain_count == 16:
        text = text.replace("ContDiff ℝ ∞", "ContDiff ℝ (∞ : ℕ∞)")
        changed = True
        print("Mock2Advanced type sixteen smoothness orders explicitly: applied 16")
    elif typed_count >= 16:
        print("Mock2Advanced type sixteen smoothness orders explicitly: already applied")
    else:
        raise RuntimeError(
            f"Mock2Advanced ContDiff infinity count unexpected: plain={plain_count}, typed={typed_count}"
        )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """  rw [UpperHalfPlane.modular_T_zpow_smul]
  rw [UpperHalfPlane.ext_iff]
  simp [gammaTwoStandardEdgeParam, UpperHalfPlane.coe_vadd]
""",
            """  rw [UpperHalfPlane.modular_T_zpow_smul]
  rw [UpperHalfPlane.ext_iff]
  apply Complex.ext <;>
    norm_num [gammaTwoStandardEdgeParam, UpperHalfPlane.coe_vadd]
""",
            1,
            "FunctionalAnalysis prove vertical side pairing componentwise",
        ),
        (
            """  · simp only [gammaTwoStandardEdgeParam, UpperHalfPlane.coe_mk,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      Complex.one_im, zero_mul, mul_zero, add_zero]
    field_simp [hd.ne']
    ring
""",
            """  · simp only [gammaTwoStandardEdgeParam, UpperHalfPlane.coe_mk,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      Complex.one_im, zero_mul, mul_zero, add_zero]
    norm_num
    field_simp [hd.ne']
    ring_nf
""",
            2,
            "FunctionalAnalysis normalize both circular pairing components",
        ),
        (
            """def gammaTwoCuspEndHeight (e : GammaTwoCuspEnd) (z : ℍ) : ℝ :=
""",
            """noncomputable def gammaTwoCuspEndHeight (e : GammaTwoCuspEnd) (z : ℍ) : ℝ :=
""",
            1,
            "FunctionalAnalysis mark cusp-end height noncomputable",
        ),
        (
            """theorem gammaTwoCuspEndHeight_continuous (e : GammaTwoCuspEnd) :
    Continuous (gammaTwoCuspEndHeight e) :=
  UpperHalfPlane.continuous_im.comp
    (continuous_const_smul (gammaTwoCuspEndScaling e)⁻¹)
""",
            """theorem gammaTwoCuspEndHeight_continuous (e : GammaTwoCuspEnd) :
    Continuous (gammaTwoCuspEndHeight e) := by
  change Continuous (fun z : ℍ =>
    ((((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
      ((gammaTwoCuspEndScaling e)⁻¹)) • z).im))
  exact UpperHalfPlane.continuous_im.comp
    (continuous_const_smul
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
        ((gammaTwoCuspEndScaling e)⁻¹)))
""",
            1,
            "FunctionalAnalysis prove cusp-end continuity through the SL2R action",
        ),
    ])


def main() -> int:
    pass109.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
