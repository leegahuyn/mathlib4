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


def replace_block(text: str, start: str, end: str, replacement: str, label: str) -> str:
    start_count = text.count(start)
    end_count = text.count(end)
    if start_count != 1 or end_count != 1:
        raise RuntimeError(
            f"{label}: expected unique markers, found start={start_count}, end={end_count}"
        )
    i = text.index(start)
    j = text.index(end, i)
    print(f"{label}: applied 1")
    return text[:i] + replacement + text[j:]


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    text = replace_block(
        text,
        "/-- Restriction naturality of `∇⁽q⁾ ⊗ id`, derived termwise. -/\n",
        "/-- Restriction naturality of `id ⊗ d_q`, derived termwise. -/\n",
        '''/-- Restriction naturality of `∇⁽q⁾ ⊗ id`, derived termwise. -/
theorem nablaTensorId_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (nablaTensorId P V z) =
      nablaTensorId P U ((aqPresheaf E F).res hUV z) := by
  have hmap :
      (tensorRestriction (aqPresheaf E F)
          (omega1Presheaf (X := X)) hUV).comp
          (nablaTensorId P V) =
        (nablaTensorId P U).comp
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV) := by
    apply TensorProduct.ext'
    intro l m
    change
      TensorProduct.map
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV)
          (locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV)
          ((pointwiseOperator P.qPotential V l ⊗ₜ[ℂ] m) ⊗ₜ[ℂ]
            dlogFrame V) =
        ((pointwiseOperator P.qPotential U
              (locallyConstantRestriction E hUV l) ⊗ₜ[ℂ]
            locallyConstantRestriction F hUV m) ⊗ₜ[ℂ]
          dlogFrame U)
    rw [TensorProduct.map_tmul]
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
  exact LinearMap.congr_fun hmap z

''',
        "Mock2 rebuild nabla naturality from the established coefficient theorem",
    )
    text = replace_block(
        text,
        "/-- Restriction naturality of `id ⊗ d_q`, derived termwise. -/\n",
        "/-- The constructed Definition 13 derivative commutes with restriction.",
        '''/-- Restriction naturality of `id ⊗ d_q`, derived termwise. -/
theorem idTensorDq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (idTensorDq P V z) =
      idTensorDq P U ((aqPresheaf E F).res hUV z) := by
  have hmap :
      (tensorRestriction (aqPresheaf E F)
          (omega1Presheaf (X := X)) hUV).comp
          (idTensorDq P V) =
        (idTensorDq P U).comp
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV) := by
    apply TensorProduct.ext'
    intro l m
    change
      TensorProduct.map
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV)
          (locallyConstantRestriction (ModuleCat.of ℂ ℂ) hUV)
          ((l ⊗ₜ[ℂ] pointwiseOperator P.logDerivative V m) ⊗ₜ[ℂ]
            dlogFrame V) =
        ((locallyConstantRestriction E hUV l ⊗ₜ[ℂ]
            pointwiseOperator P.logDerivative U
              (locallyConstantRestriction F hUV m)) ⊗ₜ[ℂ]
          dlogFrame U)
    rw [TensorProduct.map_tmul]
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
  exact LinearMap.congr_fun hmap z

''',
        "Mock2 rebuild logarithmic naturality from the established coefficient theorem",
    )
    text = replace_block(
        text,
        "/-- The constructed Definition 13 derivative commutes with restriction.",
        "/-! ### Complex linearity and the full scalar Leibniz rule -/\n",
        '''/-- The constructed Definition 13 derivative commutes with restriction.  This
is a theorem derived from the two pointwise fibre operators and the logarithmic
frame, not a field of the derivative. -/
theorem Dq_restrict {E F : ModuleCat ℂ}
    (P : FibreOperators E F) {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (z : AqSection E F V) :
    (aqOmega1Presheaf E F).res hUV (Dq P V z) =
      Dq P U ((aqPresheaf E F).res hUV z) := by
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (nablaTensorId P V z + idTensorDq P V z) =
      nablaTensorId P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z) +
        idTensorDq P U
          (tensorRestriction (locallyConstantLinearPresheaf E)
            (locallyConstantLinearPresheaf F) hUV z)
  have hn := nablaTensorId_restrict (X := X) P hUV z
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (nablaTensorId P V z) =
      nablaTensorId P U
        (tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV z) at hn
  have hi := idTensorDq_restrict (X := X) P hUV z
  change
    tensorRestriction (aqPresheaf E F) (omega1Presheaf (X := X)) hUV
        (idTensorDq P V z) =
      idTensorDq P U
        (tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV z) at hi
  rw [(tensorRestriction (aqPresheaf E F)
    (omega1Presheaf (X := X)) hUV).map_add, hn, hi]

''',
        "Mock2 derive Dq naturality from the two raw-carrier summands",
    )
    path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            '''  map_add' x y := by
    dsimp
    rw [map_add, map_add]
    abel
''',
            '''  map_add' x y := by
    change
      ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N))
          (x.1 + y.1) -
        ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N))
          (x.2 + y.2) =
      (ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N)) x.1 -
        ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N)) x.2) +
      (ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N)) y.1 -
        ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N)) y.2)
    rw [map_add, map_add]
    abel
''',
            1,
            "Mock2Advanced retain bundled cast homomorphisms in CRT additivity",
        ),
        (
            '''    have hzero :
        ((za - zb : ℤ) : ZMod (Nat.gcd M N)) = 0 := by
      simpa [crtObstructionMap] using h
''',
            '''    have hzero :
        ((za - zb : ℤ) : ZMod (Nat.gcd M N)) = 0 := by
      simpa [crtObstructionMap, ZMod.castHom_apply,
        ZMod.cast_intCast] using h
''',
            1,
            "Mock2Advanced normalize both CRT casts of integer representatives",
        ),
        (
            '''  · rintro ⟨z, rfl⟩
    simp [crtObstructionMap]
''',
            '''  · rintro ⟨z, hz⟩
    rw [← hz]
    simp [crtObstructionMap, comparisonMap_apply,
      ZMod.castHom_apply, ZMod.cast_intCast]
''',
            1,
            "Mock2Advanced rewrite the exactness witness instead of dependent subst",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            '''  (RealSmooth.contDiffAt_upperLift hu z).of_le (by exact le_top)
''',
            '''  (RealSmooth.contDiffAt_upperLift hu z).of_le
    (show (2 : ℕ∞ω) ≤ ∞ from le_top)
''',
            1,
            "FunctionalAnalysis use the native finite-infinity smoothness order",
        ),
        (
            '''  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (by exact le_top)).iteratedFDeriv_cons
''',
            '''  exact ((RealSmooth.contDiffAt_upperLift hu z).isSymmSndFDerivAt
    (show minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) from le_top)).iteratedFDeriv_cons
''',
            1,
            "FunctionalAnalysis type the minSmoothness comparison explicitly",
        ),
        (
            '''  simp only [star_add, star_mul', star_div, star_neg,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
  field_simp [hh] <;> ring
''',
            '''  simp only [map_add, map_mul, map_inv, map_neg, star_div,
    Complex.conj_I, conj_physicalExponent, conj_heightC]
  field_simp [hh] <;> ring
''',
            1,
            "FunctionalAnalysis expose star as the complex conjugation homomorphism",
        ),
        (
            '''  change RealSmooth (fun z => q * (heightC z)⁻¹)
  simpa only [Pi.smul_apply, smul_eq_mul] using
    RealSmooth.const_complex_smul q hInv
''',
            '''  change RealSmooth (fun z => q * (heightC z)⁻¹)
  rw [show (fun z => q * (heightC z)⁻¹) =
      q • (fun z => (heightC z)⁻¹) by
    funext z
    rfl]
  exact RealSmooth.const_complex_smul q hInv
''',
            1,
            "FunctionalAnalysis identify constant scalar multiplication extensionally",
        ),
        (
            '''      change d1 (fun w => q * (heightC w)⁻¹) z ξ =
        q * d1 (fun w => (heightC w)⁻¹) z ξ
      simpa only [Pi.smul_apply, smul_eq_mul] using
        d1_smul q hInv z ξ
''',
            '''      change d1 (fun w => q * (heightC w)⁻¹) z ξ =
        q * d1 (fun w => (heightC w)⁻¹) z ξ
      rw [show (fun w => q * (heightC w)⁻¹) =
          q • (fun w => (heightC w)⁻¹) by
        funext w
        rfl]
      exact d1_smul q hInv z ξ
''',
            1,
            "FunctionalAnalysis identify the scalar derivative function extensionally",
        ),
        (
            '''  rw [dx_add (hNeg.mul hdx) (hs.mul hdy),
''',
            '''  rw [dx_add (RealSmooth.mul hNeg hdx) (RealSmooth.mul hs hdy),
''',
            1,
            "FunctionalAnalysis use the project RealSmooth multiplication theorem in dx",
        ),
        (
            '''  rw [dy_add (hNeg.mul hdx) (hs.mul hdy),
''',
            '''  rw [dy_add (RealSmooth.mul hNeg hdx) (RealSmooth.mul hs hdy),
''',
            1,
            "FunctionalAnalysis use the project RealSmooth multiplication theorem in dy",
        ),
    ])


def main() -> int:
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
