from __future__ import annotations

from pathlib import Path

import apply_sixty_third_pass_repairs as pass63

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass63.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start_marker = "\nnamespace AdvancedClaimsIIRequirement\n\ndef leafStatement\n"
    end_marker = "\nend AdvancedClaimsIIRequirement\n\nstructure AdvancedClaimsIIRequirementDispatchCertificate"
    insert_marker = "\ndef statement\n    (C : AdvancedClaimsIICompletionCertificate)"
    if start_marker in text:
        start = text.index(start_marker)
        end = text.index(end_marker, start)
        block = text[start:end + len("\nend AdvancedClaimsIIRequirement\n")]
        text = text[:start] + "\n\nstructure AdvancedClaimsIIRequirementDispatchCertificate" + text[end + len(end_marker):]
        if insert_marker not in text:
            raise RuntimeError("Mock1Advanced prompt statement insertion point missing")
        pos = text.index(insert_marker)
        text = text[:pos] + block + "\n" + text[pos:]
        changed = True
        print("Mock1Advanced move leafStatement before its first use: applied")
    else:
        first_use = text.find("AdvancedClaimsIIRequirement.leafStatement C (requirementOf b)")
        declaration = text.find("def leafStatement\n    (C : AdvancedClaimsIICompletionCertificate)")
        if declaration < 0 or first_use < 0 or declaration > first_use:
            raise RuntimeError("Mock1Advanced leafStatement declaration ordering not repaired")
        print("Mock1Advanced move leafStatement before its first use: already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """            simp only [Nat.cast_mul, Nat.cast_pow, Int.cast_mul, Int.cast_natCast]
            ac_rfl
""",
            """            simp only [Nat.cast_mul, Nat.cast_pow, Int.cast_mul, Int.cast_pow,
              Int.cast_natCast]
            ac_rfl
""",
            "Mock2 normalize integer powers before AC reordering",
        ),
        (
            """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    exact hz.trans (map_zero (integerMul M)).symm
""",
            """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    change (M : ℤ) * (z : ℤ) = (M : ℤ) * (0 : ℤ)
    change (M : ℤ) * (z : ℤ) = 0 at hz
    simpa using hz
""",
            "Mock2 expose multiplication-by-M on zero as integer arithmetic",
        ),
        (
            """@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  change ChainComplex.of.d freeResolutionX (freeResolutionD M) (n + 3) (n + 2) = 0
  rw [ChainComplex.of_d]
  rfl
""",
            """@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  change ChainComplex.of.d freeResolutionX (freeResolutionD M)
    ((n + 2) + 1) (n + 2) = 0
  rw [ChainComplex.of_d]
  rfl
""",
            "Mock2 present the higher differential in successor normal form",
        ),
        (
            """    ⟨residueProjection M, by
      simpa using integerMul_comp_residueProjection M⟩
""",
            """    ⟨residueProjection M, by
      convert integerMul_comp_residueProjection M using 1 <;> rfl⟩
""",
            "Mock2 identify the augmentation compatibility up to proof irrelevance",
        ),
        (
            """    HomologicalComplex.QuasiIso (freeResolutionAugmentation M) where
""",
            """    QuasiIso (freeResolutionAugmentation M) where
""",
            "Mock2 use the current unqualified QuasiIso class",
        ),
        (
            """  augmentation_quasiIso :
    HomologicalComplex.QuasiIso (freeResolutionAugmentation M)
""",
            """  augmentation_quasiIso :
    QuasiIso (freeResolutionAugmentation M)
""",
            "Mock2 use the current QuasiIso class in the comparison certificate",
        ),
        (
            """  rw [freeResolutionComplex_d_one_zero]
""",
            """  rw [freeResolutionComplex_d_one_zero]
  rfl
""",
            "Mock2 close the tensor differential identity after rewriting",
        ),
        (
            """  change (tensorRightFunctor N).map ((freeResolutionComplex M).d 2 1) = 0
  simp
""",
            """  change (tensorRightFunctor N).map ((freeResolutionComplex M).d 2 1) = 0
  rw [freeResolutionComplex_d_two_one]
  exact (tensorRightFunctor N).map_zero
""",
            "Mock2 use functorial preservation of the zero differential",
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
            """def restrict {U V : TopologicalSpace.Opens X} (hVU : V ≤ U) :
    sections U →ₗ[ℂ] sections V where
""",
            """def restrict {U V : TopologicalSpace.Opens X} (hVU : V ≤ U) :
    sections (X := X) (Fiber := Fiber) U →ₗ[ℂ]
      sections (X := X) (Fiber := Fiber) V where
""",
            "Mock2Advanced expose both ambient types in trivial-bundle restriction",
        ),
        (
            """    (f : sections U) (x : X) :
    ((restrict hVU f : sections V) : X → Fiber) x =
""",
            """    (f : sections (X := X) (Fiber := Fiber) U) (x : X) :
    ((TrivialBundleSectionSheaf.restrict (X := X) (Fiber := Fiber) hVU f :
        sections (X := X) (Fiber := Fiber) V) : X → Fiber) x =
""",
            "Mock2Advanced disambiguate the concrete restriction theorem",
        ),
        (
            """noncomputable def sectionsEquivLocalFunctions
    (U : TopologicalSpace.Opens X) :
    sections (X := X) (Fiber := Fiber) U ≃ₗ[ℂ] (U → Fiber) := by
  classical
  refine
    { toFun := fun f x => (f : X → Fiber) x.1
      invFun := fun g =>
        ⟨fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0,
          by
            intro x hx
            simp [hx]⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro f
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ U
    · simp [hx]
    · simp [hx, f.property x hx]
  · intro g
    funext x
    simp [x.property]
  · intro f g
    funext x
    rfl
  · intro c f
    funext x
    rfl
""",
            """noncomputable def sectionsEquivLocalFunctions
    (U : TopologicalSpace.Opens X) :
    sections (X := X) (Fiber := Fiber) U ≃ₗ[ℂ] (U → Fiber) := by
  classical
  refine
    { toFun := fun f x => (f : X → Fiber) x.1
      invFun := fun g =>
        ⟨fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0,
          by
            intro x hx
            simp [hx]⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ U
        · simp [hx]
        · simp [hx, f.property x hx]
      right_inv := by
        intro g
        funext x
        simp [x.property]
      map_add' := by
        intro f g
        funext x
        rfl
      map_smul' := by
        intro c f
        funext x
        rfl }
""",
            "Mock2Advanced attach each linear-equivalence proof to its named field",
        ),
        (
            """def presheaf : LinearPresheaf X (X → Fiber) where
  section := sections
""",
            """def presheaf : LinearPresheaf X (X → Fiber) where
  «section» := sections (X := X) (Fiber := Fiber)
""",
            "Mock2Advanced initialize the escaped section field explicitly",
        ),
        (
            """  restrict := fun {_ _} h => restrict h
""",
            """  restrict := fun {_ _} h =>
    TrivialBundleSectionSheaf.restrict (X := X) (Fiber := Fiber) h
""",
            "Mock2Advanced disambiguate the presheaf restriction map",
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

    text, did = replace_exact(
        text,
        """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  <;> ring
""",
        """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
""",
        1,
        "FunctionalAnalysis cancel the remaining intermediate eta factor explicitly",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """namespace WeightSection

variable {M : HalfIntegralMultiplier Γ k}

@[simp]
""",
        """namespace WeightSection

variable {M : HalfIntegralMultiplier Γ k}

instance instCoeFun : CoeFun (WeightSection M) (fun _ => ℍ → ℂ) where
  coe u := u.1

@[simp]
""",
        1,
        "FunctionalAnalysis expose covariant weight sections as functions",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass63.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
