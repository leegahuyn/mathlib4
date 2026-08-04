from __future__ import annotations

from pathlib import Path
import base64
import re
import zlib

import apply_sixty_fifth_pass_repairs as pass65

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass65.replace_exact
M1_STRUCTURES = """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"""


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start_marker = "\nnamespace AdvancedClaimsIIRequirement\n\ndef leafStatement"
    if start_marker in text:
        start = text.index(start_marker)
        end = text.index("\nend AdvancedClaimsIIRequirement", start) + len("\nend AdvancedClaimsIIRequirement")
        block = text[start:end]
        text = text[:start] + text[end:]
        insert = text.index("\nnamespace AdvancedClaimsIIPromptBullet\n")
        text = text[:insert] + block + "\n" + text[insert:]
        changed = True
        print("Mock1Advanced move leafStatement to the top-level requirement namespace: applied")
    else:
        top = text.index("namespace AdvancedClaimsIIRequirement\n\ndef leafStatement")
        prompt = text.index("namespace AdvancedClaimsIIPromptBullet")
        if top < prompt:
            print("Mock1Advanced move leafStatement to the top-level requirement namespace: already applied")
        else:
            raise RuntimeError("Mock1Advanced leafStatement namespace layout not recognized")

    first_structure = "structure AdvancedClaimsIIPromptObjectiveAuditCertificate"
    if first_structure not in text:
        block = zlib.decompress(base64.b64decode(M1_STRUCTURES)).decode("utf-8")
        marker = "structure AdvancedClaimsIIClaimGroupLeafStatementCertificate"
        pos = text.index(marker)
        text = text[:pos] + block + text[pos:]
        changed = True
        print("Mock1Advanced restore five missing prompt and claim-group audit structures: applied")
    else:
        print("Mock1Advanced restore five missing prompt and claim-group audit structures: already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    simpa [integerMul_apply] using hz
"""
    new = """  have hz0 : z = 0 := by
    change (M : ℤ) * (z : ℤ) = 0 at hz
    have hMZ : (M : ℤ) ≠ 0 := by exact_mod_cast hM
    exact (mul_eq_zero.mp hz).resolve_left hMZ
"""
    text, did = replace_exact(text, old, new, 1,
        "Mock2 prove degree-one exactness directly in the integers")
    changed |= did

    old = """  rw [freeResolutionComplex_d_two_one]
  simpa using (tensorRightFunctor N).map_zero
    (freeResolutionX 2) (freeResolutionX 1)
"""
    new = """  rw [freeResolutionComplex_d_two_one]
  simpa only [Functor.map_zero]
"""
    text, did = replace_exact(text, old, new, 1,
        "Mock2 use the functor zero-map simplification without explicit object arguments")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """      if x ∈ V then (f : X → Fiber) x else 0 :=
  rfl
"""
    new = """      if x ∈ V then (f : X → Fiber) x else 0 := by
  classical
  rfl
"""
    text, did = replace_exact(text, old, new, 1,
        "Mock2Advanced install classical membership in restrict_apply")
    changed |= did

    old = """  locality := by
    intro ι U V hVU hcover s t hlocal
"""
    new = """  locality := by
    classical
    intro ι U V hVU hcover s t hlocal
"""
    text, did = replace_exact(text, old, new, 1,
        "Mock2Advanced install classical membership in concrete locality")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  field_simp [ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
"""
    new = """  ring
"""
    text, did = replace_exact(text, old, new, 1,
        "FunctionalAnalysis finish the eta quotient identity after denominator clearing")
    changed |= did

    old = """      rw [div_zpow, div_eq_mul_inv, ← zpow_neg b k]
      ac_rfl
"""
    new = """      rw [div_zpow, div_eq_mul_inv, ← zpow_neg b k]
      ring
"""
    text, did = replace_exact(text, old, new, 1,
        "FunctionalAnalysis reorder eta powers with ring normalization")
    changed |= did

    old = """  scale_covariance : ∀ γ z,
    scale ((γ : SL(2, ℤ)) • z) * ‖M.factor γ z‖ ^ 2 = scale z
"""
    new = """  scale_covariance : ∀ (γ : Γ) z,
    scale ((γ : SL(2, ℤ)) • z) * ‖M.factor γ z‖ ^ 2 = scale z
"""
    text, did = replace_exact(text, old, new, 1,
        "FunctionalAnalysis bind fiber-metric covariance to the subgroup")
    changed |= did

    for name in ("pointwiseNormSq", "pointwiseInnerDensity"):
        old = f"def {name} (m : InvariantFiberMetric M)"
        new = f"noncomputable def {name} (m : InvariantFiberMetric M)"
        text, did = replace_exact(text, old, new, 1,
            f"FunctionalAnalysis mark {name} noncomputable")
        changed |= did

    new_text, count = re.subn(r"Complex\.conj(?=[ (])", "star", text)
    if count:
        text = new_text
        changed = True
        print(f"FunctionalAnalysis replace removed Complex.conj function with star: applied {count}")
    elif "Complex.conj (" not in text and "Complex.conj c" not in text:
        print("FunctionalAnalysis replace removed Complex.conj function with star: already applied")
    else:
        raise RuntimeError("FunctionalAnalysis Complex.conj replacement state not recognized")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass65.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
