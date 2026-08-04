from __future__ import annotations

from pathlib import Path

import apply_eighty_second_pass_repairs as pass82
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("namespace GenuineWeightedSobolev")
    end = text.index("end GenuineWeightedSobolev", start)
    block = text[start:end]
    old_namespace = "GenuineInverseHalfWeightAutomorphy."
    new_namespace = "GenuineHalfWeightAutomorphy."
    count = block.count(old_namespace)
    if count:
        block = block.replace(old_namespace, new_namespace)
        text = text[:start] + block + text[end:]
        changed = True
        print(
            "Mock2Advanced preserve the half-weight Sobolev convention: "
            f"applied {count}"
        )
    elif new_namespace in block:
        print(
            "Mock2Advanced preserve the half-weight Sobolev convention: "
            "already applied"
        )
    else:
        raise RuntimeError(
            "Mock2Advanced weighted Sobolev automorphy qualification absent"
        )

    text, did = replace_exact(
        text,
        """theorem pSeriesMajorant_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (pSeriesMajorant δ) := by
  simpa only [pSeriesMajorant] using
    (Real.summable_one_div_nat_add_rpow 1 (1 + δ)).2 (by linarith)
""",
        """theorem pSeriesMajorant_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (pSeriesMajorant δ) := by
  change Summable (fun n : ℕ =>
    1 / |(n : ℝ) + 1| ^ (1 + δ))
  exact (Real.summable_one_div_nat_add_rpow 1 (1 + δ)).2 (by linarith)
""",
        1,
        "Mock2Advanced expose the p-series majorant before convergence",
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
    ModularForm.eta_ne_zero ((γ * δ) • z).2] <;>
    field_simp [ModularForm.eta_ne_zero z.2,
      ModularForm.eta_ne_zero (δ • z).2,
      ModularForm.eta_ne_zero ((γ * δ) • z).2] <;> ring
""",
        """  simp only [div_eq_mul_inv]
  calc
    ModularForm.eta ↑z * (ModularForm.eta ↑(γ • δ • z))⁻¹ =
        (ModularForm.eta ↑(δ • z) *
          (ModularForm.eta ↑(δ • z))⁻¹) *
            (ModularForm.eta ↑z *
              (ModularForm.eta ↑(γ • δ • z))⁻¹) := by
      rw [mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), one_mul]
    _ =
        (ModularForm.eta ↑(δ • z) *
          (ModularForm.eta ↑(γ • δ • z))⁻¹) *
            (ModularForm.eta ↑z *
              (ModularForm.eta ↑(δ • z))⁻¹) := by ring
""",
        1,
        "FunctionalAnalysis prove the inverse-eta cocycle by direct cancellation",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass82.main()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
