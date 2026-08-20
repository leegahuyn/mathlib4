from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(text: str, old: str, new: str, expected: int, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == expected:
        print(f"{label}: applied {count}")
        return text.replace(old, new), True
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count == 0:
        print(f"{label}: source changed; skipped")
        return text, False
    raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """theorem mem_all
    (b : AdvancedClaimsIIPromptBullet) :
    List.Mem b all := by
  cases b <;> simp [all]
""",
        """theorem mem_all
    (b : AdvancedClaimsIIPromptBullet) :
    List.Mem b all := by
  cases b <;> decide
""",
        1,
        "Mock1Advanced decide prompt-bullet membership after constructor analysis",
    )
    changed |= did

    old = """end AdvancedClaimsIIPromptBulletDispatchCertificate

structure AdvancedClaimsIIClaimGroupLeafStatementCertificate
"""
    new = """end AdvancedClaimsIIPromptBullet

structure AdvancedClaimsIIRequirementDispatchCertificate
    (C : AdvancedClaimsIICompletionCertificate) : Prop where
  leaf_ledger :
    AdvancedClaimsIIRequirementLeafLedger C
  requirement_covered :
    forall r, List.Mem r C.requirements
  leaf_statement :
    forall r, AdvancedClaimsIIRequirement.leafStatement C r

namespace AdvancedClaimsIIRequirementDispatchCertificate

theorem leaf_ledger_at
    {C : AdvancedClaimsIICompletionCertificate}
    (D : AdvancedClaimsIIRequirementDispatchCertificate C) :
    AdvancedClaimsIIRequirementLeafLedger C :=
  D.leaf_ledger

theorem requirement_covered_at
    {C : AdvancedClaimsIICompletionCertificate}
    (D : AdvancedClaimsIIRequirementDispatchCertificate C)
    (r : AdvancedClaimsIIRequirement) :
    List.Mem r C.requirements :=
  D.requirement_covered r

theorem leaf_statement_at
    {C : AdvancedClaimsIICompletionCertificate}
    (D : AdvancedClaimsIIRequirementDispatchCertificate C)
    (r : AdvancedClaimsIIRequirement) :
    AdvancedClaimsIIRequirement.leafStatement C r :=
  D.leaf_statement r

end AdvancedClaimsIIRequirementDispatchCertificate

structure AdvancedClaimsIIClaimGroupLeafStatementCertificate
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock1Advanced restore the requirement dispatch certificate deleted by pass 61",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring_nf
""",
        """            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ac_rfl
""",
        1,
        "Mock2 close the reordered prime-power product by associativity and commutativity",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    rw [map_zero]
    exact hz
""",
        """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    simpa [integerMul_apply] using hz
""",
        1,
        "Mock2 compare multiplication by M with its value at zero",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl
""",
        """@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  change freeResolutionD M (n + 2) = 0
  rfl
""",
        1,
        "Mock2 expose the higher free-resolution differential definitionally",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  · exact ModuleCat.projective_of_free (Basis.singleton Unit ℤ)
  · exact ModuleCat.projective_of_free (Basis.singleton Unit ℤ)
  · apply CategoryTheory.Limits.IsZero.projective
    exact (CategoryTheory.Limits.isZero_zero :
      CategoryTheory.Limits.IsZero zeroIntegerModule)
""",
        """  · exact ModuleCat.projective_of_free (Module.Basis.singleton Unit ℤ)
  · exact ModuleCat.projective_of_free (Module.Basis.singleton Unit ℤ)
  · apply CategoryTheory.Limits.IsZero.projective
    exact ModuleCat.isZero_of_subsingleton zeroIntegerModule
""",
        1,
        "Mock2 use the current singleton basis and concrete zero-module APIs",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  simpa using
    (CategoryTheory.Limits.isZero_zero :
      CategoryTheory.Limits.IsZero zeroIntegerModule)
""",
        """  exact ModuleCat.isZero_of_subsingleton zeroIntegerModule
""",
        1,
        "Mock2 prove higher exactness from the concrete zero module",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """    (factor T hT f).app U («include».app U s) = f.app U s
""",
            """    (factor (G' := G') T hT f).app U («include».app U s) = f.app U s
""",
            1,
            "Mock2Advanced fix the sheafification factor universe in factor_include",
        ),
        (
            """    g = factor T hT f
""",
            """    g = factor (G' := G') T hT f
""",
            1,
            "Mock2Advanced fix the sheafification factor universe in factor_unique",
        ),
        (
            """  refine ⟨S.factor T hT f, ?_, ?_⟩
""",
            """  refine ⟨S.factor (G' := G') T hT f, ?_, ?_⟩
""",
            1,
            "Mock2Advanced instantiate the factor universe in existsUnique",
        ),
        (
            """  apply hP.locality V hVU hcover
""",
            """  apply hP.locality (ι := ι) (U := U) V hVU hcover
""",
            1,
            "Mock2Advanced fix the equalizer-locality index universe",
        ),
        (
            """  obtain ⟨u, hu⟩ := hP.gluing V hVU hcover
    (fun i => (s i : P.section (V i))) hcompatP
""",
            """  obtain ⟨u, hu⟩ := hP.gluing (ι := ι) (U := U) V hVU hcover
    (fun i => (s i : P.section (V i))) hcompatP
""",
            1,
            "Mock2Advanced fix the equalizer-gluing index universe",
        ),
        (
            """  sheaf_condition : IsLinearSheaf forms
""",
            """  sheaf_condition : IsLinearSheaf (X := X) (E := E) forms
""",
            1,
            "Mock2Advanced pin the gauge-descent sheaf universe parameters",
        ),
    ]
    for old, new, expected, label in replacements:
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """    exact (Complex.continuousAt_sqrt (Or.inr him)).comp' hdenom
""",
        """    exact ContinuousAt.comp'
      (f := fun w : ℍ ↦ UpperHalfPlane.denom g w)
      (g := Complex.sqrt)
      (Complex.continuousAt_sqrt (Or.inr him)) hdenom
""",
        1,
        "FunctionalAnalysis force the upper-half-plane domain in sqrt continuity",
    )
    changed |= did

    old = """    simpa [CuspForm.discriminant, ModularForm.discriminant] using
      (SlashInvariantForm.slash_action_eqn''
        CuspForm.discriminant
        (show (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨γ, rfl⟩) z)
"""
    new = """    have hΔ := SlashInvariantForm.slash_action_eqn''
      CuspForm.discriminant
      (show (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨γ, rfl⟩) z
    change ModularForm.discriminant (((γ : SL(2, ℤ)) • z : ℍ)) =
      UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z ^ 12 *
        ModularForm.discriminant z at hΔ
    simpa only [ModularForm.discriminant] using hΔ
"""
    text, did = replace_exact(
        text, old, new, 1,
        "FunctionalAnalysis expose the discriminant function before eta normalization",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  <;> ring
""",
        """  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
""",
        1,
        "FunctionalAnalysis cancel the intermediate eta value directly",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  nu_one := by
    simp only [etaPhase_one, inv_one, one_zpow]
""",
        """  nu_one := by
    change ((etaPhase (1 : SL(2, ℤ)))⁻¹) ^ k = 1
    rw [etaPhase_one, inv_one, one_zpow]
""",
        1,
        "FunctionalAnalysis expose the subgroup identity in nu_one",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """    simpa only [inverseEtaRawFactor_zpow] using h
""",
        """    simpa only [inverseEtaRawFactor_zpow, map_mul] using h
""",
        1,
        "FunctionalAnalysis normalize the subgroup-product coercion in the factor cocycle",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
