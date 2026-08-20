from __future__ import annotations

from pathlib import Path

import apply_one_hundred_thirty_seventh_pass_repairs as pass137
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
            """@[simp] theorem omega1Presheaf_res_apply
    {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (ω : (omega1Presheaf (X := X)).obj V) (x : U) :
    (omega1Presheaf (X := X)).res hUV ω x =
      ω ⟨x.1, hUV x.2⟩ :=
  rfl
""",
            """@[simp] theorem omega1Presheaf_res_apply
    {U V : TopologicalSpace.Opens X} (hUV : U ≤ V)
    (ω : (omega1Presheaf (X := X)).obj V) (x : U) :
    ((((omega1Presheaf (X := X)).res hUV ω :
        LocallyConstant U ℂ).toFun x)) =
      (ω : LocallyConstant V ℂ).toFun ⟨x.1, hUV x.2⟩ :=
  rfl
""",
            1,
            "Mock2 expose the locally constant carrier in omega-one restriction",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  · simp [smoothVolumeUnitData]

/-- The active spectral set""",
            """  · change volume.restrict (Ioo (-δ) δ) =
      volume.restrict (Ioo (-δ) δ)
    rfl

/-- The active spectral set""",
            1,
            "Mock2Advanced reduce the concrete spectral measure to volume definitionally",
        ),
        (
            """theorem discreteSeries_contribution_pos (m : ℕ) :
    0 < discreteSeries.contribution m := by
  exact (discreteSeries_term_pos m).trans_le
""",
            """theorem discreteSeries_contribution_pos (m : ℕ) :
    0 < discreteSeries.contribution m := by
  classical
  exact (discreteSeries_term_pos m).trans_le
""",
            1,
            "Mock2Advanced provide decidable equality for the concrete one-mode series",
        ),
        (
            """theorem selectedMode_add_mass_le_spectralSide (m : ℕ) :
    spectralData.test 0 + massFunctional spectralData m ≤
      seriesIdentity.spectralSide m := by
  simpa only [normalization_factor, one_mul, discreteSeries_term] using
""",
            """theorem selectedMode_add_mass_le_spectralSide (m : ℕ) :
    spectralData.test 0 + massFunctional spectralData m ≤
      seriesIdentity.spectralSide m := by
  classical
  simpa only [normalization_factor, one_mul, discreteSeries_term] using
""",
            1,
            "Mock2Advanced provide decidable equality for selected-mode isolation",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """    have hfloor :
        ⌊(((n + 2 : ℕ) : ℝ))⌋₊ = n + 2 := by
      exact Nat.floor_natCast (R := ℝ) (n + 2)
    simpa [gammaTwoTopologicalTruncation, hfloor] using
      hn.trans (hstage.trans (Set.image_mono hmono))
""",
            """    change K ⊆ gammaTwoQuotientMk ''
      gammaTwoCompactLiftExhaustion ⌊(((n + 2 : ℕ) : ℝ))⌋₊
    rw [Nat.floor_natCast]
    exact hn.trans (hstage.trans (Set.image_mono hmono))
""",
            1,
            "FunctionalAnalysis rewrite the truncation stage directly at the goal",
        ),
    ])


def main() -> int:
    pass137.main()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
