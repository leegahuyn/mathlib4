from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """  rw [← htau]
  rw [(contDiffWithinAt_localInvariantProp
    (I := 𝓘(ℂ))
    (I' := 𝓘(ℂ, OneFormValue I_G G)) ∞).liftPropAt_iff_comp_inclusion
      (coverOpen_mono (C.piece_le_target i))]
  exact hlocal tau_i
""",
        """  rw [← htau]
  have hpoint :
      ChartedSpace.LiftPropAt
        (ContDiffWithinAtProp
          𝓘(ℂ) 𝓘(ℂ, OneFormValue I_G G) ∞)
        (strictGluedToFun I_G G C s)
        (SmoothOneForm.coverInclusion (C.piece_le_target i) tau_i) := by
    rw [(contDiffWithinAt_localInvariantProp
      (I := 𝓘(ℂ))
      (I' := 𝓘(ℂ, OneFormValue I_G G)) ∞).liftPropAt_iff_comp_inclusion
        (coverOpen_mono (C.piece_le_target i))]
    exact hlocal tau_i
  exact hpoint
""",
        "Mock2 transport local smoothness through the open inclusion",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
