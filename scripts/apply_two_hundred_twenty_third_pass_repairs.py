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
""",
        """/- `TangentSpace` deliberately hides the model-space norm from typeclass
inference.  In this section we use the fixed chart model `E_G`, so install the
transported normed structures locally rather than adding assumptions to the
public API. -/
noncomputable local instance gaugeLieAlgebraNormedAddCommGroup :
    NormedAddCommGroup (GaugeLieAlgebra I_G G) := by
  change NormedAddCommGroup E_G
  infer_instance

noncomputable local instance gaugeLieAlgebraNormedSpace :
    NormedSpace ℂ (GaugeLieAlgebra I_G G) := by
  change NormedSpace ℂ E_G
  infer_instance

/-- Value of a `𝔤`-valued one-form in the complex chart of `ℍ`. -/
abbrev OneFormValue := ℂ →L[ℂ] GaugeLieAlgebra I_G G
""",
        "Mock2 install the model-space norm on the Lie algebra locally",
    )
    m2 = replace_exact(
        m2,
        """theorem ext_pointwise {U : Opens} {A B : SmoothOneForm I_G G U}
    (h : ∀ τ : coverOpen U, A τ = B τ) : A = B :=
  ext (funext h)
""",
        """theorem ext_pointwise {U : Opens} {A B : SmoothOneForm I_G G U}
    (h : ∀ τ : coverOpen U, A τ = B τ) : A = B :=
  SmoothOneForm.ext (I_G := I_G) (G := G) (funext h)
""",
        "Mock2 disambiguate the smooth one-form extensionality theorem",
    )
    M2.write_text(m2, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
