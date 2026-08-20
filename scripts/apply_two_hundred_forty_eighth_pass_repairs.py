from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


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
        """abbrev OneFormValue
    (I_G : ModelWithCorners ℂ E_G H_G) (G : Type uGG) :=
  ℂ →L[ℂ] GaugeLieAlgebra I_G G

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        """abbrev OneFormValue
    (I_G : ModelWithCorners ℂ E_G H_G) (G : Type uGG) :=
  ℂ →L[ℂ] GaugeLieAlgebra I_G G

noncomputable local instance oneFormValueNormedAddCommGroup :
    NormedAddCommGroup (OneFormValue I_G G) := by
  change NormedAddCommGroup (ℂ →L[ℂ] GaugeLieAlgebra I_G G)
  infer_instance

noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] GaugeLieAlgebra I_G G)
  infer_instance

noncomputable local instance oneFormValueCoeFun :
    CoeFun (OneFormValue I_G G)
      (fun _ => ℂ → GaugeLieAlgebra I_G G) where
  coe L := fun z =>
    (show ℂ →L[ℂ] GaugeLieAlgebra I_G G from L) z

/-- Smooth `𝔤`-valued one-forms on the actual open submanifold `π⁻¹(U)`. -/
""",
        "Mock2 restore the one-form CLM structures and coercion",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  letI : NontriviallyNormedField ℂ :=
    Complex.instNormedField.toNontriviallyNormedField
""",
        """  letI : NontriviallyNormedField ℂ :=
    Complex.instDenselyNormedField.toNontriviallyNormedField
""",
        "Mock2 Advanced use the dense complex field projection",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hu := u.2 FixedPhaseDifferentialWord.nil γ z
  have hv := v.2 FixedPhaseDifferentialWord.nil γ z
  simp only [FixedPhaseDifferentialWord.targetIndex_nil,
    FixedPhaseDifferentialWord.eval_nil_apply] at hu hv
  have hu' :
      ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        F * (u : SmoothQuotientCompactFunction) z := by
    simpa [F, M, OrbitMultiplier,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction] using hu
  have hv' :
      ((v : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        (F * j ^ 2) * (v : SmoothQuotientCompactFunction) z := by
    have hFactor := inverseEtaPaperOrbitMultiplier_factor_add_one
      GammaTwo n γ z
    rw [hFactor] at hv
    simpa [F, M, j, OrbitMultiplier, mul_assoc,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction] using hv
""",
        """  have hu := u.2 FixedPhaseDifferentialWord.nil γ z
  have hv := v.2 FixedPhaseDifferentialWord.nil γ z
  have hu0 :
      ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        (OrbitMultiplier n).factor γ z *
          (u : SmoothQuotientCompactFunction) z := by
    simpa [OrbitMultiplier,
      FixedPhaseDifferentialWord.targetIndex_nil,
      FixedPhaseDifferentialWord.eval_nil_apply,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction] using hu
  have hv0 :
      ((v : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        (OrbitMultiplier (n + 1)).factor γ z *
          (v : SmoothQuotientCompactFunction) z := by
    simpa [OrbitMultiplier,
      FixedPhaseDifferentialWord.targetIndex_nil,
      FixedPhaseDifferentialWord.eval_nil_apply,
      InverseEtaFixedPhaseCore.toSmoothQuotientCompactFunction] using hv
  have hu' :
      ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        F * (u : SmoothQuotientCompactFunction) z := by
    simpa [F, M] using hu0
  have hv' :
      ((v : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        (F * j ^ 2) * (v : SmoothQuotientCompactFunction) z := by
    have hFactor := inverseEtaPaperOrbitMultiplier_factor_add_one
      GammaTwo n γ z
    rw [hFactor] at hv0
    simpa [F, M, j, OrbitMultiplier, mul_assoc] using hv0
""",
        "FunctionalAnalysis isolate nil-word covariance before reindexing",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
