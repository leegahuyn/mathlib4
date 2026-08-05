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


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """    change
      tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
          (pointwiseOperator P.qPotential V l ⊗ₜ[ℂ] m) =
        pointwiseOperator P.qPotential U
            ((locallyConstantLinearPresheaf E).res hUV l) ⊗ₜ[ℂ]
          ((locallyConstantLinearPresheaf F).res hUV m)
    rw [tensorRestriction_tmul, pointwiseOperator_restrict]
""",
            """    change
      TensorProduct.map
          (locallyConstantRestriction E hUV)
          (locallyConstantRestriction F hUV)
          (pointwiseOperator P.qPotential V l ⊗ₜ[ℂ] m) =
        pointwiseOperator P.qPotential U
            (locallyConstantRestriction E hUV l) ⊗ₜ[ℂ]
          (locallyConstantRestriction F hUV m)
    rw [TensorProduct.map_tmul, pointwiseOperator_restrict]
""",
            1,
            "Mock2 expose potential-coefficient restriction through concrete tensor maps",
        ),
        (
            """    change
      tensorRestriction (locallyConstantLinearPresheaf E)
          (locallyConstantLinearPresheaf F) hUV
          (l ⊗ₜ[ℂ] pointwiseOperator P.logDerivative V m) =
        ((locallyConstantLinearPresheaf E).res hUV l) ⊗ₜ[ℂ]
          pointwiseOperator P.logDerivative U
            ((locallyConstantLinearPresheaf F).res hUV m)
    rw [tensorRestriction_tmul, pointwiseOperator_restrict]
""",
            """    change
      TensorProduct.map
          (locallyConstantRestriction E hUV)
          (locallyConstantRestriction F hUV)
          (l ⊗ₜ[ℂ] pointwiseOperator P.logDerivative V m) =
        locallyConstantRestriction E hUV l ⊗ₜ[ℂ]
          pointwiseOperator P.logDerivative U
            (locallyConstantRestriction F hUV m)
    rw [TensorProduct.map_tmul, pointwiseOperator_restrict]
""",
            1,
            "Mock2 expose logarithmic-coefficient restriction through concrete tensor maps",
        ),
    ])


def main() -> int:
    repair_mock2()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
