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
            """    rw [TensorProduct.map_tmul]
    have hpot := potentialCoefficient_restrict
      (X := X) P hUV (l ⊗ₜ[ℂ] m)
    have hpot' :
        tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV
            (pointwiseOperator P.qPotential V l ⊗ₜ[ℂ] m) =
          pointwiseOperator P.qPotential U
              (locallyConstantRestriction E hUV l) ⊗ₜ[ℂ]
            locallyConstantRestriction F hUV m := by
      simpa only [potentialCoefficient_tmul, tensorRestriction_tmul] using hpot
    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    rw [hpot', hframe]
""",
            """    have hpot := pointwiseOperator_restrict
      (X := X) P.qPotential hUV l
    change
      locallyConstantRestriction E hUV
          (pointwiseOperator P.qPotential V l) =
        pointwiseOperator P.qPotential U
          (locallyConstantRestriction E hUV l) at hpot
    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    simpa only [TensorProduct.map_tmul, tensorRestriction_tmul, hpot, hframe]
""",
            1,
            "Mock2 simplify both tensor layers in nabla naturality",
        ),
        (
            """    rw [TensorProduct.map_tmul]
    have hlog := logRadialCoefficient_restrict
      (X := X) P hUV (l ⊗ₜ[ℂ] m)
    have hlog' :
        tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV
            (l ⊗ₜ[ℂ] pointwiseOperator P.logDerivative V m) =
          locallyConstantRestriction E hUV l ⊗ₜ[ℂ]
            pointwiseOperator P.logDerivative U
              (locallyConstantRestriction F hUV m) := by
      simpa only [logRadialCoefficient_tmul, tensorRestriction_tmul] using hlog
    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    rw [hlog', hframe]
""",
            """    have hlog := pointwiseOperator_restrict
      (X := X) P.logDerivative hUV m
    change
      locallyConstantRestriction F hUV
          (pointwiseOperator P.logDerivative V m) =
        pointwiseOperator P.logDerivative U
          (locallyConstantRestriction F hUV m) at hlog
    have hframe := dlogFrame_restrict (X := X) hUV
    change
      locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV (dlogFrame V) =
        dlogFrame U at hframe
    simpa only [TensorProduct.map_tmul, tensorRestriction_tmul, hlog, hframe]
""",
            1,
            "Mock2 simplify both tensor layers in logarithmic naturality",
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
  change
    (aqOmega1Presheaf E F).res hUV
        (nablaTensorId P V z + idTensorDq P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z) +
        idTensorDq P U ((aqPresheaf E F).res hUV z)
  rw [map_add, nablaTensorId_restrict, idTensorDq_restrict]

""",
        "Mock2 prove full derivative naturality in the categorical carrier",
    )


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """    have hzero :
        ((za - zb : ℤ) : ZMod (Nat.gcd M N)) = 0 := by
      simpa [crtObstructionMap, ZMod.castHom_apply,
        ZMod.cast_intCast] using h
""",
            """    have hzero :
        ((za - zb : ℤ) : ZMod (Nat.gcd M N)) = 0 := by
      change
        (ZMod.cast (za : ZMod M) : ZMod (Nat.gcd M N)) -
          (ZMod.cast (zb : ZMod N) : ZMod (Nat.gcd M N)) = 0 at h
      rw [ZMod.cast_intCast (Nat.gcd_dvd_left M N),
        ZMod.cast_intCast (Nat.gcd_dvd_right M N)] at h
      rw [Int.cast_sub]
      exact h
""",
            1,
            "Mock2Advanced transport CRT integer casts explicitly",
        ),
        (
            """  · rintro ⟨z, hz⟩
    rw [← hz]
    change
      (ZMod.cast (z : ZMod M) : ZMod (Nat.gcd M N)) -
        (ZMod.cast (z : ZMod N) : ZMod (Nat.gcd M N)) = 0
    rw [ZMod.cast_intCast (Nat.gcd_dvd_left M N),
      ZMod.cast_intCast (Nat.gcd_dvd_right M N)]
    exact sub_self _
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
            "Mock2Advanced retain the explicit CRT image witness",
        ),
        (
            "open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory\n",
            "open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory\nopen scoped ZeroObject\n",
            1,
            "Mock2Advanced enable the chosen categorical zero object",
        ),
        (
            "  simp [cyclicFreeComplex, ChainComplex.mk'_d, cyclicFreeSuccessor]\n",
            "  simp [cyclicFreeComplex, ChainComplex.mk'_d, cyclicFreeSuccessor] <;> rfl\n",
            1,
            "Mock2Advanced close the definitionally zero successor differential",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            "    (show (2 : ℕ∞ω) ≤ ∞ from le_top)\n",
            "    (show (2 : ℕ∞ω) ≤ ∞ by simp)\n",
            1,
            "FunctionalAnalysis prove finite smoothness lies below infinity",
        ),
        (
            """    (show minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) from le_top)).iteratedFDeriv_cons
""",
            """    (show minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) by
      simp [minSmoothness])).iteratedFDeriv_cons
""",
            1,
            "FunctionalAnalysis simplify the minimum smoothness order",
        ),
        (
            """  unfold raiseRaw lowerRaw
  simp only [map_add, map_mul, map_inv, map_neg, star_div,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
  field_simp [hh] <;> ring
""",
            """  simp only [raiseRaw, lowerRaw, map_add, map_mul, map_neg,
    map_pow, star_div, Complex.conj_I, conj_physicalExponent,
    conj_heightC]
  field_simp [hh] <;> ring
""",
            1,
            "FunctionalAnalysis unfold the Green identity inside simplification",
        ),
        (
            """  unfold heightSq
  ring
""",
            """  unfold heightSq
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
""",
            2,
            "FunctionalAnalysis expose pointwise scalar multiplication in lower derivatives",
        ),
        (
            "  rw [hf.mixedDerivative_comm z, sub_self, mul_zero, add_zero] at h\n",
            "  rw [mixedDerivative_comm hf z, sub_self, mul_zero, add_zero] at h\n",
            2,
            "FunctionalAnalysis call mixed derivative symmetry without field notation",
        ),
        (
            """  have hLR := lower_raise_factorization hf z
  have hRL := raise_lower_factorization hf z
""",
            """  have hLR := lower_raise_factorization (a := a) hf z
  have hRL := raise_lower_factorization (a := a) hf z
""",
            1,
            "FunctionalAnalysis determine the exponent in averaged factorization",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
