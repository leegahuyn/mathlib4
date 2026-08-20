from __future__ import annotations

from pathlib import Path

import apply_one_hundred_twenty_eighth_pass_repairs as pass128
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


def repair_mock1_advanced() -> None:
    apply_replacements(ROOT / "Mock1_Advanced.lean", [
        (
            """structure AdvancedClaimsIIAbstractConcreteCertificationBridgeCertificate :
    Prop where
""",
            """structure AdvancedClaimsIIAbstractConcreteCertificationBridgeCertificate :
    Type where
""",
            1,
            "Mock1Advanced place the data-bearing abstract-concrete bridge in Type",
        ),
        (
            """    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Prop where
  unconditional_readiness :
""",
            """    (hrow :
      List.Mem row
        referenceAdvancedClaimsIICompletionCertificate.tables.paperTables.externalScript.rows) :
    Type where
  unconditional_readiness :
""",
            1,
            "Mock1Advanced place the data-bearing microlocal readiness certificate in Type",
        ),
    ])


def repair_mock2() -> None:
    apply_replacements(ROOT / "Mock2.lean", [
        (
            """    intro i
    rw [← e.naturality (C.piece_le_target i) x]
    rw [← e.naturality (C.piece_le_target i) y]
    rw [hxy i]
""",
            """    intro i
    change
      G.res (C.piece_le_target i) (e.app C.target x) =
        G.res (C.piece_le_target i) (e.app C.target y)
    rw [← e.naturality (C.piece_le_target i) x]
    rw [← e.naturality (C.piece_le_target i) y]
    exact congrArg (e.app (C.piece i)) (hxy i)
""",
            1,
            "Mock2 expose concrete restrictions before transporting locality through naturality",
        ),
        (
            """      rw [← e.naturality, ← e.naturality, hs i j]
""",
            """      rw [← e.naturality, ← e.naturality]
      exact congrArg (e.app (C.piece i ⊓ C.piece j)) (hs i j)
""",
            1,
            "Mock2 transport gluing compatibility through the fibre equivalence explicitly",
        ),
    ])


def repair_mock2_advanced() -> None:
    apply_replacements(ROOT / "Mock2_Advanced.lean", [
        (
            """  apply integrable_dirac
  simp [kernel]
  exact pow_pos (by norm_num) i
""",
            """  apply integrable_dirac
  simp [kernel]
  exact pos_iff_ne_zero.mpr (pow_ne_zero i (by norm_num))
""",
            1,
            "Mock2Advanced prove ENNReal power positivity via nonvanishing",
        ),
    ])


def repair_functional_analysis() -> None:
    apply_replacements(ROOT / "Mock2_FunctionalAnalysis.lean", [
        (
            """ℝ[X]""",
            """Polynomial ℝ""",
            8,
            "FunctionalAnalysis replace unavailable polynomial notation by the explicit type",
        ),
    ])


def main() -> int:
    pass128.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
