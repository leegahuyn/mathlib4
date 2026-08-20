from __future__ import annotations

from pathlib import Path

import apply_one_hundred_fifty_third_pass_repairs as pass153
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


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  flat_minimizer_mass_remainder_zero D hmass hremainder A A₀ hflat
    (D.action_eq_zero_of_flat_vacuum hflat₀ hmass₀ hremainder₀) hmin
""",
            """  flat_minimizer_mass_remainder_zero D hmass hremainder A A₀ hflat
    (EffectiveActionDecomposition.action_eq_zero_of_flat_vacuum
      D hflat₀ hmass₀ hremainder₀) hmin
""",
            1,
            "Mock2Advanced call flat-vacuum action vanishing explicitly",
        ),
        (
            """  D.covariant_gluing_existsUnique V hVU hcover s.1 s.2
""",
            """  simpa only using
    D.covariant_gluing_existsUnique (ι := ι) (U := U)
      V hVU hcover (fun i => s.1 i) (fun i j => s.2 i j)
""",
            1,
            "Mock2Advanced determine gauge gluing family and universes explicitly",
        ),
        (
            """theorem restrictionToCompatibleGaugeFamily_injective
    {X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type*} (D : GaugeDescentSheaf X E)
    {U : TopologicalSpace.Opens X}
    (V : ι → TopologicalSpace.Opens X)
    (hVU : ∀ i, V i ≤ U)
    (hcover : U ≤ ⨆ i, V i) :
    Function.Injective (restrictionToCompatibleGaugeFamily D V hVU) := by
  intro u v huv
  apply Subtype.ext
  apply D.sheaf_condition.locality V hVU hcover
""",
            """theorem restrictionToCompatibleGaugeFamily_injective
    {X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E]
    {ι : Type*} (D : GaugeDescentSheaf X E)
    {U : TopologicalSpace.Opens X}
    (V : ι → TopologicalSpace.Opens X)
    (hVU : ∀ i, V i ≤ U)
    (hcover : U ≤ ⨆ i, V i) :
    Function.Injective (restrictionToCompatibleGaugeFamily D V hVU) := by
  intro u v huv
  apply Subtype.ext
  apply D.sheaf_condition.locality (ι := ι) (U := U)
    V hVU hcover
""",
            1,
            "Mock2Advanced determine locality cover universes in the restriction injection theorem",
        ),
    ])


def main() -> int:
    pass153.repair_mock2()
    repair_mock2_advanced()
    pass153.repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
