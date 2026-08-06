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
        """/-- Value of a `𝔤`-valued one-form in the complex chart of `ℍ`. -/
abbrev OneFormValue := ℂ →L[ℂ] GaugeLieAlgebra I_G G

noncomputable local instance oneFormValueNormedAddCommGroup :
    NormedAddCommGroup (OneFormValue I_G G) := by
  change NormedAddCommGroup (ℂ →L[ℂ] E_G)
  infer_instance

noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] E_G)
  infer_instance

""",
        """/-- Value of a `𝔤`-valued one-form in the complex chart of `ℍ`.
The public parameters are retained, while the representation is exposed as
its actual chart model so Mathlib can infer the canonical CLM structures. -/
abbrev OneFormValue
    (_I_G : ModelWithCorners ℂ E_G H_G) (_G : Type uGG) :=
  ℂ →L[ℂ] E_G

""",
        "Mock2 expose the one-form value chart model without changing its public name",
    )
    m2 = replace_exact(
        m2,
        """  line_action_smooth :
    ∀ γ : Gamma2, CMDiff ∞ (lineSmul M γ)
""",
        """  line_action_smooth :
    ∀ γ : Gamma2,
      ContMDiff ((𝓘(ℂ)).prod (𝓘(ℂ)))
        ((𝓘(ℂ)).prod (𝓘(ℂ))) ∞ (lineSmul M γ)
""",
        "Mock2 state the line-action smoothness models explicitly",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
