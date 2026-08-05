from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(
    text: str, old: str, new: str, label: str, expected: int = 1
) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(
            f"{label}: expected exactly {expected} match(es), found {count}"
        )
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """/-- The tangent map of a deck transformation in the complex chart. -/
def deckTangent (γ : Gamma2) (τ : H) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.lsmul ℂ ℂ (deckDerivative γ τ)

@[simp] theorem deckTangent_apply
    (γ : Gamma2) (τ : H) (v : ℂ) :
    deckTangent γ τ v = deckDerivative γ τ * v := by
  simp [deckTangent, smul_eq_mul]

theorem deckTangent_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞ (deckTangent γ) := by
  exact (ContinuousLinearMap.lsmul ℂ ℂ).contMDiff.comp
    (deckDerivative_contMDiff γ)
""",
        """/-- The tangent map of a deck transformation in the complex chart. -/
def deckTangent (γ : Gamma2) (τ : H) : ℂ →L[ℂ] ℂ :=
  deckDerivative γ τ • ContinuousLinearMap.id ℂ ℂ

@[simp] theorem deckTangent_apply
    (γ : Gamma2) (τ : H) (v : ℂ) :
    deckTangent γ τ v = deckDerivative γ τ * v := by
  simp [deckTangent, smul_eq_mul]

theorem deckTangent_contMDiff (γ : Gamma2) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞ (deckTangent γ) := by
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
    (fun τ : H => deckDerivative γ τ • ContinuousLinearMap.id ℂ ℂ)
  exact (deckDerivative_contMDiff γ).smul contMDiff_const
""",
        "Mock2 express the deck tangent as scalar multiplication of the identity map",
    )
    m2 = replace_exact(
        m2,
        """  have hmem :
      gammaGL γ ∈ (Matrix.SpecialLinearGroup.mapGL ℝ).range := by
    exact ⟨γ.1, rfl⟩
""",
        """  have hmem :
      gammaGL γ ∈
        ((Matrix.SpecialLinearGroup.mapGL ℝ :
          SL(2, ℤ) →* GL (Fin 2) ℝ).range) := by
    exact ⟨γ.1, rfl⟩
""",
        "Mock2 fix the source ring of the special-linear image",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  unfold modularLeftVerticalCurve
  convert
    ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
      (-(1 : ℝ) / 2 : ℂ)) using 1 <;>
    simp [add_comm]
""",
        """theorem hasDerivAt_modularLeftVerticalCurve (t : ℝ) :
    HasDerivAt modularLeftVerticalCurve Complex.I t := by
  change HasDerivAt
    (fun x : ℝ => (-(1 : ℝ) / 2 : ℂ) + Complex.I * (x : ℂ))
    Complex.I t
  simpa [Complex.ofRealCLM_apply, smul_eq_mul] using
    ((Complex.I • Complex.ofRealCLM).hasDerivAt (x := t)).const_add
      (-(1 : ℝ) / 2 : ℂ)
""",
        "Mock2 Advanced differentiate the left affine curve through ofRealCLM",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  unfold modularRightVerticalCurve
  convert
    ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
      ((1 : ℝ) / 2 : ℂ)) using 1 <;>
    simp [add_comm]
""",
        """theorem hasDerivAt_modularRightVerticalCurve (t : ℝ) :
    HasDerivAt modularRightVerticalCurve Complex.I t := by
  change HasDerivAt
    (fun x : ℝ => ((1 : ℝ) / 2 : ℂ) + Complex.I * (x : ℂ))
    Complex.I t
  simpa [Complex.ofRealCLM_apply, smul_eq_mul] using
    ((Complex.I • Complex.ofRealCLM).hasDerivAt (x := t)).const_add
      ((1 : ℝ) / 2 : ℂ)
""",
        "Mock2 Advanced differentiate the right affine curve through ofRealCLM",
    )
    m2a = replace_exact(
        m2a,
        """theorem contDiff_modularLeftVerticalCurve :
    ContDiff ℝ (↑(⊤ : ℕ∞)) modularLeftVerticalCurve := by
  unfold modularLeftVerticalCurve
  fun_prop
""",
        """theorem contDiff_modularLeftVerticalCurve :
    ContDiff ℝ (↑(⊤ : ℕ∞)) modularLeftVerticalCurve := by
  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun x : ℝ => (-(1 : ℝ) / 2 : ℂ) + Complex.I * (x : ℂ))
  simpa [Complex.ofRealCLM_apply, smul_eq_mul] using
    ((Complex.I • Complex.ofRealCLM).contDiff.const_add
      (-(1 : ℝ) / 2 : ℂ))
""",
        "Mock2 Advanced prove left affine smoothness through ofRealCLM",
    )
    m2a = replace_exact(
        m2a,
        """theorem contDiff_modularRightVerticalCurve :
    ContDiff ℝ (↑(⊤ : ℕ∞)) modularRightVerticalCurve := by
  unfold modularRightVerticalCurve
  fun_prop
""",
        """theorem contDiff_modularRightVerticalCurve :
    ContDiff ℝ (↑(⊤ : ℕ∞)) modularRightVerticalCurve := by
  change ContDiff ℝ (↑(⊤ : ℕ∞))
    (fun x : ℝ => ((1 : ℝ) / 2 : ℂ) + Complex.I * (x : ℂ))
  simpa [Complex.ofRealCLM_apply, smul_eq_mul] using
    ((Complex.I • Complex.ofRealCLM).contDiff.const_add
      ((1 : ℝ) / 2 : ℂ))
""",
        "Mock2 Advanced prove right affine smoothness through ofRealCLM",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """      Bw = star (j ^ 2) *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [map_inv₀]
        field_simp [hjc]
""",
        """      Bw = star (j ^ 2) *
          (star ((j ^ 2)⁻¹) * Bw) := by
        field_simp [hjc]
""",
        "FunctionalAnalysis cancel the already-normalized conjugate inverse directly",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
