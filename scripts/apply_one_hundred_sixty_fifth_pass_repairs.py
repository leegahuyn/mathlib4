from pathlib import Path
import apply_seventy_first_pass_repairs as p

F = Path("PrimalitySheafVerification/Mock2.lean")


def main():
    s = F.read_text(encoding="utf-8")
    edits = [
        ("theorem certificate (E F : ModuleCat ℂ) (P : FibreOperators E F) :\n    Certificate E F P := by\n",
         "theorem certificate (E F : ModuleCat ℂ) (P : FibreOperators E F) :\n    Certificate (X := X) E F P := by\n",
         "certificate base"),
        ("theorem actual_certificate\n    (D : Definition11.AnalyticData V) (A : Set ℂ)\n    (P : ActualFibreOperators D A) :\n    Certificate (ActualLqFibre D) (ActualMmockFibre A) P :=\n  certificate (ActualLqFibre D) (ActualMmockFibre A) P\n",
         "theorem actual_certificate\n    (D : Definition11.AnalyticData V) (A : Set ℂ)\n    (P : ActualFibreOperators D A) :\n    Certificate (X := Definition11.RadiusBase)\n      (ActualLqFibre D) (ActualMmockFibre A) P :=\n  certificate (X := Definition11.RadiusBase)\n    (ActualLqFibre D) (ActualMmockFibre A) P\n",
         "actual certificate base"),
        ("theorem corrected_certificate\n    (D : Definition11.AnalyticData V) (A : Set ℂ) :\n    Certificate (ActualLqFibre D) (ActualMmockFibre A)\n      (zeroActualFibreOperators D A) :=\n  actual_certificate D A (zeroActualFibreOperators D A)\n",
         "theorem corrected_certificate\n    (D : Definition11.AnalyticData V) (A : Set ℂ) :\n    Certificate (X := Definition11.RadiusBase)\n      (ActualLqFibre D) (ActualMmockFibre A)\n      (zeroActualFibreOperators D A) :=\n  actual_certificate D A (zeroActualFibreOperators D A)\n",
         "corrected certificate base"),
        ("    { predicate_restriction_stable := fun hUV hA =>\n        modularCovariance_restrict Aq MC hMC hUV hA\n",
         "    { predicate_restriction_stable := fun hUV hA =>\n        modularCovariance_restrict (Aq := Aq) (MC := MC) hMC hUV hA\n",
         "modular covariance args"),
    ]
    for old, new, label in edits:
        s, _ = p.replace_exact(s, old, new, 1, label)
    F.write_text(s, encoding="utf-8", newline="\n")
    return 0

if __name__ == "__main__": raise SystemExit(main())
