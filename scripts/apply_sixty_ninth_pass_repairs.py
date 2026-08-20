from __future__ import annotations

from pathlib import Path
import re

import apply_sixty_eighth_pass_repairs as pass68

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass68.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    pattern = re.compile(
        r"  · simp \[requirementOf, "
        r"AdvancedClaimsIIRequirement\.[A-Za-z0-9_]+Requirements\]"
    )
    text, count = pattern.subn("  · decide", text)
    if count:
        if count != 51:
            raise RuntimeError(
                f"Mock1Advanced expected 51 finite bridge branches, found {count}")
        changed = True
        print("Mock1Advanced discharge 51 concrete requirement-list branches by decide: applied")
    elif text.count("  · decide") >= 51:
        print("Mock1Advanced discharge 51 concrete requirement-list branches by decide: already applied")
    else:
        raise RuntimeError("Mock1Advanced requirement bridge branch pattern absent")

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
    simpa only [map_zero] using hz
""",
            """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    rw [map_zero]
    exact hz
""",
            "Mock2 orient the image-of-zero equation before applying injectivity",
        ),
        (
            """  intro z x
  change (M : ℤ) • ((z : ℤ) • x) = ((M : ℤ) * (z : ℤ)) • x
  rw [smul_smul]
""",
            """  intro z x
  let z' : ℤ := z
  change (M : ℤ) • (z' • x) = ((M : ℤ) * z') • x
  rw [smul_smul]
""",
            "Mock2 name the tensor-unit element as an integer before scalar action",
        ),
        (
            """noncomputable def tensorResolutionXTwoIsoZero (M N : ℕ) :
    (tensorResolutionComplex M N).X 2 ≅ zeroIntegerModule := by
  exact (tensorResolutionComplex_X_add_two_isZero M N 0).isoZero
""",
            """noncomputable def tensorResolutionXTwoIsoZero (M N : ℕ) :
    (tensorResolutionComplex M N).X 2 ≅ zeroIntegerModule := by
  exact (tensorResolutionComplex_X_add_two_isZero M N 0).iso
    (ModuleCat.isZero_of_subsingleton zeroIntegerModule)
""",
            "Mock2 identify the two explicit zero objects by IsZero.iso",
        ),
        (
            """      rw [tensorResolutionComplex_d_two_one]
      simp)
""",
            """      rw [tensorResolutionComplex_d_two_one]
      rw [zero_comp])
""",
            "Mock2 close the zero differential square with zero_comp",
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

    old = """      have hji :
          (s j : X → Fiber) x = (s i : X → Fiber) x := by
        simpa [presheaf, restrict_apply, hxj, hxi] using hvalue
"""
    new = """      have hji :
          (s j : X → Fiber) x = (s i : X → Fiber) x := by
        change
          ((TrivialBundleSectionSheaf.restrict
              (X := X) (Fiber := Fiber) inf_le_left (s j) :
              sections (X := X) (Fiber := Fiber) (V j ⊓ V i)) : X → Fiber) x =
            ((TrivialBundleSectionSheaf.restrict
              (X := X) (Fiber := Fiber) inf_le_right (s i) :
              sections (X := X) (Fiber := Fiber) (V j ⊓ V i)) : X → Fiber) x
          at hvalue
        rw [restrict_apply, restrict_apply] at hvalue
        simpa [hxj, hxi] using hvalue
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2Advanced expose both overlap restrictions before point evaluation")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
