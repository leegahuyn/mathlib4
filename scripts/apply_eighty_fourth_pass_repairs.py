from __future__ import annotations

from pathlib import Path

import apply_seventy_eighth_pass_repairs as pass78
import apply_eighty_second_pass_repairs as pass82
import apply_eightieth_pass_repairs as pass80
import apply_eighty_third_pass_repairs as pass83
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock2_advanced() -> None:
    pass80.repair_mock2_advanced()

    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("namespace GenuineWeightedSobolev")
    end = text.index("end GenuineWeightedSobolev", start)
    block = text[start:end]
    old = "exact (M.core_equivariant v hv).isAE)"
    new = "exact (M.core_equivariant v hv).isAE μ)"
    count = block.count(old)
    if count == 1:
        block = block.replace(old, new, 1)
        text = text[:start] + block + text[end:]
        changed = True
        print("Mock2Advanced supply μ in the inverse-half-weight Sobolev block: applied 1")
    elif count == 0 and new in block:
        print("Mock2Advanced supply μ in the inverse-half-weight Sobolev block: already applied")
    else:
        raise RuntimeError(
            f"Mock2Advanced expected one inverse-half-weight isAE projection, found {count}"
        )

    text, did = replace_exact(
        text,
        """  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      simp only [abelRemainder] at ih ⊢
      ring
""",
        """  | succ N ih =>
      unfold abelRemainder at ih ⊢
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        prefixSum_succ]
      ring
""",
        1,
        "Mock2Advanced unfold Abel remainders before rewriting the induction hypothesis",
    )
    changed |= did

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


def main() -> int:
    pass78.main()
    pass82.repair_mock1_advanced()
    pass82.repair_mock2()
    repair_mock2_advanced()
    pass82.repair_functional_analysis()
    pass83.repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
