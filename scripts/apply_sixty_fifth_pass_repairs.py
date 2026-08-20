from __future__ import annotations

from pathlib import Path
import re

import apply_sixty_fourth_pass_repairs as pass64

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass64.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("def leafStatement\n    (C : AdvancedClaimsIICompletionCertificate)")
    end = text.index("\nend AdvancedClaimsIIRequirement", start)
    block = text[start:end]
    pattern = re.compile(r"^  \| ([A-Za-z][A-Za-z0-9_]*) =>", re.M)
    matches = pattern.findall(block)
    if matches:
        if len(matches) != 54:
            raise RuntimeError(
                f"Mock1Advanced expected 54 unqualified leaf constructors, found {len(matches)}"
            )
        block = pattern.sub(r"  | AdvancedClaimsIIRequirement.\1 =>", block)
        text = text[:start] + block + text[end:]
        changed = True
        print("Mock1Advanced qualify all requirement constructors in leafStatement: applied 54")
    else:
        qualified = re.findall(
            r"^  \| AdvancedClaimsIIRequirement\.([A-Za-z][A-Za-z0-9_]*) =>",
            block,
            re.M,
        )
        if len(qualified) != 54:
            raise RuntimeError(
                "Mock1Advanced leafStatement constructors are neither fully unqualified nor fully qualified"
            )
        print("Mock1Advanced qualify all requirement constructors in leafStatement: already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    change (M : ℤ) * (z : ℤ) = (M : ℤ) * (0 : ℤ)
    change (M : ℤ) * (z : ℤ) = 0 at hz
    simpa using hz
""",
            """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    simpa [integerMul_apply] using hz
""",
            "Mock2 prove the degree-one kernel equation through the explicit multiplication lemma",
        ),
        (
            """@[simp] theorem freeResolutionAugmentation_f_zero (M : ℕ) :
    (freeResolutionAugmentation M).f 0 = residueProjection M := by
  simp [freeResolutionAugmentation]
""",
            """@[simp] theorem freeResolutionAugmentation_f_zero (M : ℕ) :
    (freeResolutionAugmentation M).f 0 = residueProjection M := by
  change residueProjection M = residueProjection M
  rfl
""",
            "Mock2 expose the zero-degree component of the augmentation definitionally",
        ),
        (
            """        · simpa [resolutionAtZero] using resolutionAtZero_exact M
        · rw [ModuleCat.epi_iff_surjective]
          simpa using residueProjection_surjective M
""",
            """        · convert resolutionAtZero_exact M using 1 <;> rfl
        · rw [ModuleCat.epi_iff_surjective]
          convert residueProjection_surjective M using 1 <;> rfl
""",
            "Mock2 transport the degree-zero exactness and surjectivity across proof-irrelevant wrappers",
        ),
        (
            """        rw [HomologicalComplex.quasiIsoAt_iff_exactAt'
          (hL := ChainComplex.exactAt_succ_single_obj ..)]
""",
            """        rw [quasiIsoAt_iff_exactAt'
          (hL := ChainComplex.exactAt_succ_single_obj ..)]
""",
            "Mock2 use the current top-level quasiIsoAt exactness lemma",
        ),
        (
            """  rw [freeResolutionComplex_d_two_one]
  exact (tensorRightFunctor N).map_zero
""",
            """  rw [freeResolutionComplex_d_two_one]
  simpa using (tensorRightFunctor N).map_zero
    (freeResolutionX 2) (freeResolutionX 1)
""",
            "Mock2 instantiate the source and target objects in functor map_zero",
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

    old = """def restrict {U V : TopologicalSpace.Opens X} (hVU : V ≤ U) :
    sections (X := X) (Fiber := Fiber) U →ₗ[ℂ]
      sections (X := X) (Fiber := Fiber) V where
  toFun f := ⟨fun x => if x ∈ V then (f : X → Fiber) x else 0,
    by
      intro x hx
      simp [hx]⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ V <;> simp [hx]
  map_smul' c f := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ V <;> simp [hx]
"""
    new = """noncomputable def restrict {U V : TopologicalSpace.Opens X} (hVU : V ≤ U) :
    sections (X := X) (Fiber := Fiber) U →ₗ[ℂ]
      sections (X := X) (Fiber := Fiber) V := by
  classical
  refine
    { toFun := fun f =>
        ⟨fun x => if x ∈ V then (f : X → Fiber) x else 0,
          by
            intro x hx
            simp [hx]⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ V <;> simp [hx]
  · intro c f
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ V <;> simp [hx]
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2Advanced make cutoff restriction explicitly classical and noncomputable",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """def presheaf : LinearPresheaf X (X → Fiber) where
""",
        """noncomputable def presheaf : LinearPresheaf X (X → Fiber) where
""",
        1,
        "Mock2Advanced mark the presheaf containing classical cutoff maps noncomputable",
    )
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
  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
""",
        """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  field_simp [ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
""",
        1,
        "FunctionalAnalysis clear the residual eta quotient after the first denominator pass",
    )
    changed |= did

    replacements = [
        ("u.covariance γ z", "WeightSection.covariance u γ z", 6,
         "FunctionalAnalysis qualify all six direct weight-section covariance calls"),
        ("u.factor_eq_one_of_fixed_nonzero γ z hfix hu",
         "WeightSection.factor_eq_one_of_fixed_nonzero u γ z hfix hu", 1,
         "FunctionalAnalysis qualify the fixed-point factor theorem"),
        ("v.covariance γ z", "WeightSection.covariance v γ z", 1,
         "FunctionalAnalysis qualify the paired weight-section covariance call"),
    ]
    for old, new, count, label in replacements:
        text, did = replace_exact(text, old, new, count, label)
        changed |= did

    for name in ("rawPointwiseNorm", "rawPointwiseNormSq"):
        old = f"def {name} (u : WeightSection M) (z : ℍ) : ℝ :="
        new = f"noncomputable def {name} (u : WeightSection M) (z : ℍ) : ℝ :="
        text, did = replace_exact(
            text,
            old,
            new,
            1,
            f"FunctionalAnalysis mark {name} noncomputable because Complex.norm is noncomputable",
        )
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass64.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
