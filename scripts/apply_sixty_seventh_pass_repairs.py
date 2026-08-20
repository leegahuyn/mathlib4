from __future__ import annotations

from pathlib import Path
import re

import apply_sixty_sixth_pass_repairs as pass66

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass66.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("structure AdvancedClaimsIIPromptObjectiveAuditCertificate")
    end = text.index(
        "structure AdvancedClaimsIIClaimGroupLeafStatementCertificate", start
    )
    region = text[start:end]
    pattern = re.compile(
        r"^(\s*\(A : AdvancedClaimsII[A-Za-z0-9_]+Certificate C\)) :=$",
        re.M,
    )
    region, count = pattern.subn(r"\1 : _ :=", region)
    if count:
        if count != 66:
            raise RuntimeError(
                f"Mock1Advanced expected 66 projection theorem signatures, found {count}"
            )
        text = text[:start] + region + text[end:]
        changed = True
        print("Mock1Advanced infer restored projection theorem result types: applied 66")
    elif ") : _ :=" in region:
        print("Mock1Advanced infer restored projection theorem result types: already applied")
    else:
        raise RuntimeError("Mock1Advanced restored projection theorem syntax not recognized")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  change residueMulLinear M N
      ((λ_ (residueModule N)).hom (z ⊗ₜ[ℤ] x)) =
    (λ_ (residueModule N)).hom
      ((integerMul M ▷ residueModule N) (z ⊗ₜ[ℤ] x))
  simp [residueMulLinear_apply_zsmul, integerMul_apply, smul_smul]
""",
            """  change (M : ℤ) • (z • x) = ((M : ℤ) * z) • x
  rw [smul_smul]
""",
            "Mock2 reduce tensor-left-unitor naturality to scalar associativity",
        ),
        (
            """noncomputable def tensorResolutionXTwoIsoZero (M N : ℕ) :
    (tensorResolutionComplex M N).X 2 ≅ 0 := by
""",
            """noncomputable def tensorResolutionXTwoIsoZero (M N : ℕ) :
    (tensorResolutionComplex M N).X 2 ≅ (0 : ModuleCat ℤ) := by
""",
            "Mock2 type the tensor degree-two zero object",
        ),
        (
            """      rw [tensorResolutionComplex_d_two_one]
      simp)
""",
            """      rw [tensorResolutionComplex_d_two_one]
      exact (zero_comp _).symm)
""",
            "Mock2 close the degree-two comparison square by zero_comp",
        ),
        (
            """  toFun x :=
    ⟨x.1, (Tor1CyclicModel_mem_iff M N x.1).2 (by simpa using x.2)⟩
""",
            """  toFun x :=
    ⟨x.1, (Tor1CyclicModel_mem_iff M N x.1).2 (by
      rw [← residueMulLinear_apply]
      exact x.2)⟩
""",
            "Mock2 transport linear kernel membership without simplifying proof terms",
        ),
        (
            """      mathlibTor1ZEquivCyclicModel M (Pk p k) (Nat.ne_of_gt hM) x := by
  simp [mathlibTor1ZPrimePowerCanonicalEquiv]
""",
            """      mathlibTor1ZEquivCyclicModel M (Pk p k) (Nat.ne_of_gt hM) x := by
  exact (Tor1PrimePowerCanonical.powerShiftEquiv M p k hM hp).apply_symm_apply
    (mathlibTor1ZEquivCyclicModel M (Pk p k) (Nat.ne_of_gt hM) x)
""",
            "Mock2 prove the prime-power comparison triangle by equivalence cancellation",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """      have hvalue := congrArg
        (fun q : sections (V i) => (q : X → Fiber) x) (hlocal i)
      simpa [presheaf, restrict, hxi] using hvalue
""",
            """      have hvalue := congrArg
        (fun q : sections (V i) => (q : X → Fiber) x) (hlocal i)
      change
        (if x ∈ V i then (s : X → Fiber) x else 0) =
          (if x ∈ V i then (t : X → Fiber) x else 0) at hvalue
      simpa only [hxi, if_pos] using hvalue
""",
            "Mock2Advanced expose locality cutoff values",
        ),
        (
            """      have hji :
          (s j : X → Fiber) x = (s i : X → Fiber) x := by
        simpa [presheaf, restrict, hxj, hxi] using hvalue
      simpa [presheaf, restrict, glued, hxi, hxU, j] using hji
    · have hz : (s i : X → Fiber) x = 0 :=
        (s i).property x hxi
      simpa [presheaf, restrict, hxi, hz]
""",
            """      have hji :
          (s j : X → Fiber) x = (s i : X → Fiber) x := by
        change
          (if x ∈ V j ∧ x ∈ V i then (s j : X → Fiber) x else 0) =
            (if x ∈ V j ∧ x ∈ V i then (s i : X → Fiber) x else 0) at hvalue
        simpa only [hxj, hxi, and_self, if_pos] using hvalue
      change
        (if x ∈ V i then glued x else 0) = (s i : X → Fiber) x
      simp only [hxi, if_pos, glued, hxU, j]
      exact hji
    · have hz : (s i : X → Fiber) x = 0 :=
        (s i).property x hxi
      change
        (if x ∈ V i then glued x else 0) = (s i : X → Fiber) x
      simpa only [hxi, if_false] using hz.symm
""",
            "Mock2Advanced prove gluing by explicit cutoff evaluation",
        ),
        (
            """    curvature C (-A) =
      C.backgroundCurvature - C.d A + C.wedge A A := by
  simp [curvature]
""",
            """    curvature C (-A) =
      C.backgroundCurvature - C.d A + C.wedge A A := by
  simp [curvature, sub_eq_add_neg]
""",
            "Mock2Advanced normalize subtraction in curvature negation",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  ring
""",
            """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
""",
            "FunctionalAnalysis cancel the intermediate eta factor explicitly",
        ),
        (
            """  simp only [pointwiseInnerDensity, WeightSection.add_apply, map_add]
  ring
""",
            """  simp only [pointwiseInnerDensity, WeightSection.add_apply, star_add]
  ring
""",
            "FunctionalAnalysis distribute star over addition",
        ),
        (
            """  simp only [pointwiseInnerDensity, WeightSection.smul_apply, map_mul]
  ring
""",
            """  simp only [pointwiseInnerDensity, WeightSection.smul_apply, star_mul]
  ring
""",
            "FunctionalAnalysis distribute star over scalar multiplication",
        ),
        (
            """  simp only [pointwiseInnerDensity, map_mul,
    Complex.conj_ofReal, Complex.conj_conj]
  ring
""",
            """  simp only [pointwiseInnerDensity, star_mul,
    Complex.conj_ofReal, star_star]
  ring
""",
            "FunctionalAnalysis prove Hermitian conjugate symmetry with star lemmas",
        ),
        (
            """  rw [pointwiseInnerDensity, pointwiseNormSq, mul_assoc,
    Complex.conj_mul', Complex.ofReal_mul]
""",
            """  rw [pointwiseInnerDensity, pointwiseNormSq, mul_assoc]
  change
    (m.scale z : ℂ) * ((starRingEnd ℂ) (u z) * u z) =
      (m.scale z * ‖u z‖ ^ 2 : ℝ)
  rw [Complex.conj_mul', Complex.ofReal_mul]
""",
            "FunctionalAnalysis expose the complex star-ring endomorphism on the diagonal",
        ),
        (
            """  rw [pointwiseInnerDensity, pointwiseInnerDensity,
    WeightSection.covariance u γ z, WeightSection.covariance v γ z, map_mul]
""",
            """  rw [pointwiseInnerDensity, pointwiseInnerDensity,
    WeightSection.covariance u γ z, WeightSection.covariance v γ z, star_mul]
""",
            "FunctionalAnalysis distribute star through multiplier covariance",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass66.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
