from __future__ import annotations

from pathlib import Path

import apply_one_hundred_fifty_first_pass_repairs as pass151
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
            """        rw [hfun, map_add, map_add]
      map_smul' := by
        intro c s
        funext r
        have hfun :
            (fun q => L.trivialization q ((c • s) q)) =
              c • (fun q => L.trivialization q (s q)) := by
          funext q
          simp
        rw [hfun, map_smul, map_smul] }
""",
            """        rw [hfun, map_add]
        simpa only [Pi.add_apply, map_add]
      map_smul' := by
        intro c s
        funext r
        have hfun :
            (fun q => L.trivialization q ((c • s) q)) =
              c • (fun q => L.trivialization q (s q)) := by
          funext q
          simp
        rw [hfun, map_smul]
        simpa only [Pi.smul_apply, RingHom.id_apply, map_smul] }
""",
            1,
            "Mock2Advanced finish pulled-back connection linearity pointwise",
        ),
        (
            """    T = L.transport r s := by
  ext x
  apply (L.trivialization s).injective
  rw [hT x]
  simp [QLocalSystem.transport]
""",
            """    T = L.transport r s := by
  apply LinearEquiv.ext
  intro x
  apply (L.trivialization s).injective
  rw [hT x]
  simp [QLocalSystem.transport]
""",
            1,
            "Mock2Advanced compare transports before subtype extensionality",
        ),
    ])


def main() -> int:
    pass151.repair_mock2()
    repair_mock2_advanced()
    pass151.repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
