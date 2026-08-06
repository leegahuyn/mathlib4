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
        """variable {E_G H_G G : Type*}
variable [NormedAddCommGroup E_G] [NormedSpace ℂ E_G] [CompleteSpace E_G]
variable [TopologicalSpace H_G]
variable (I_G : ModelWithCorners ℂ E_G H_G)
variable [Group G] [TopologicalSpace G] [ChartedSpace H_G G]
""",
        """variable {E_G H_G : Type*}
variable [NormedAddCommGroup E_G] [NormedSpace ℂ E_G] [CompleteSpace E_G]
variable [TopologicalSpace H_G]
variable (I_G : ModelWithCorners ℂ E_G H_G)
variable (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H_G G]
""",
        "Mock2 make the gauge group an explicit parameter after the model",
    )
    m2 = replace_exact(
        m2,
        """variable [IsManifold I_G ∞ G] [LieGroup I_G ∞ G]

/-- The Lie algebra `𝔤 = T₁G` of the selected complex Lie group. -/
""",
        """variable [IsManifold I_G ∞ G] [LieGroup I_G ∞ G]

noncomputable local instance gaugeLieGroupMinSmoothness :
    LieGroup I_G (minSmoothness ℂ 3) G :=
  LieGroup.of_le le_top

/-- The Lie algebra `𝔤 = T₁G` of the selected complex Lie group. -/
""",
        "Mock2 install the smoothness instance required by GroupLieAlgebra",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """inductive ModularBoundaryPiece
  | arc
  | left
  | right
  deriving DecidableEq, Fintype, Repr
""",
        """inductive ModularBoundaryPiece
  | arc
  | left
  | right
  deriving DecidableEq, Repr

instance : Fintype ModularBoundaryPiece where
  elems := {.arc, .left, .right}
  complete := by
    intro x
    cases x <;> simp
""",
        "Mock2 Advanced define the boundary-piece Fintype explicitly",
    )
    m2a = replace_exact(
        m2a,
        """    (hU : IsOpen U) (hcurve : ContDiffOn ℝ ∞ curve U) :
    IsOpen (trimmedCurveDomain U curve) := by
""",
        """    (hU : IsOpen U)
    (hcurve : ContDiffOn ℝ (↑(⊤ : ℕ∞)) curve U) :
    IsOpen (trimmedCurveDomain U curve) := by
""",
        "Mock2 Advanced spell out infinite differentiability for trim openness",
    )
    m2a = replace_exact(
        m2a,
        """    (hcurve : ContDiffOn ℝ ∞ curve U) :
    ContDiffOn ℝ ∞ (modularCurve g curve)
      (trimmedCurveDomain U curve) := by
  intro t ht
  have houter :
      ContDiffAt ℝ ∞ (ambientModularAction g) (curve t) := by
    simpa [ambientModularAction,
      UpperHalfPlane.ofComplex_apply_of_im_pos ht.2] using
      ((UpperHalfPlane.analyticAt_smul
          (g := realGL g) (realGL_det_pos g)
          (UpperHalfPlane.ofComplex (curve t))).contDiffAt.restrict_scalars ℝ)
""",
        """    (hcurve : ContDiffOn ℝ (↑(⊤ : ℕ∞)) curve U) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (modularCurve g curve)
      (trimmedCurveDomain U curve) := by
  intro t ht
  have houter :
      ContDiffAt ℝ (↑(⊤ : ℕ∞)) (ambientModularAction g) (curve t) := by
    change ContDiffAt ℝ (↑(⊤ : ℕ∞))
      (fun z : ℂ =>
        ((realGL g • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      (curve t)
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos ht.2] using
      ((UpperHalfPlane.analyticAt_smul
          (g := realGL g) (realGL_det_pos g)
          (UpperHalfPlane.ofComplex (curve t))).contDiffAt.restrict_scalars ℝ)
""",
        "Mock2 Advanced expose the ambient modular action in smoothness",
    )
    m2a = replace_exact(
        m2a,
        """  have houter :
      HasFDerivAt (ambientModularAction g)
        (UpperHalfPlane.smulFDeriv (realGL g) (curve t))
        (curve t) := by
    simpa [ambientModularAction,
      UpperHalfPlane.ofComplex_apply_of_im_pos ht.2] using
      ((UpperHalfPlane.hasStrictFDerivAt_smul
          (realGL g) (UpperHalfPlane.ofComplex (curve t))).hasFDerivAt)
""",
        """  have houter :
      HasFDerivAt (ambientModularAction g)
        (UpperHalfPlane.smulFDeriv (realGL g) (curve t))
        (curve t) := by
    change HasFDerivAt
      (fun z : ℂ =>
        ((realGL g • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
      (UpperHalfPlane.smulFDeriv (realGL g) (curve t))
      (curve t)
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos ht.2] using
      ((UpperHalfPlane.hasStrictFDerivAt_smul
          (realGL g) (UpperHalfPlane.ofComplex (curve t))).hasFDerivAt)
""",
        "Mock2 Advanced expose the ambient modular action in differentiation",
    )
    m2a = replace_exact(
        m2a,
        """  have hfactor :
      (realGL g).det.val /
          UpperHalfPlane.denom (realGL g) (curve t) ^ 2 ≠ 0 :=
    div_ne_zero (ne_of_gt (realGL_det_pos g))
      (pow_ne_zero 2 hdenom)
""",
        """  have hdet : ((realGL g).det.val : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (realGL_det_pos g))
  have hfactor :
      (realGL g).det.val /
          UpperHalfPlane.denom (realGL g) (curve t) ^ 2 ≠ 0 :=
    div_ne_zero hdet (pow_ne_zero 2 hdenom)
""",
        "Mock2 Advanced coerce determinant nonvanishing into complex scalars",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """        calc
          Bw = 1 * Bw := by rw [one_mul]
          _ = (star (j ^ 2) * star (j ^ 2)⁻¹) * Bw :=
            congrArg (fun z : ℂ => z * Bw) (mul_inv_cancel₀ hs).symm
          _ = star (j ^ 2) * (star (j ^ 2)⁻¹ * Bw) :=
            mul_assoc _ _ _
""",
        """        have hstarInv :
            star ((j ^ 2)⁻¹) = (star (j ^ 2))⁻¹ := by
          change (starRingEnd ℂ) ((j ^ 2)⁻¹) =
            ((starRingEnd ℂ) (j ^ 2))⁻¹
          rw [map_inv₀]
        calc
          Bw = 1 * Bw := by rw [one_mul]
          _ = (star (j ^ 2) * (star (j ^ 2))⁻¹) * Bw :=
            congrArg (fun z : ℂ => z * Bw) (mul_inv_cancel₀ hs).symm
          _ = star (j ^ 2) * ((star (j ^ 2))⁻¹ * Bw) :=
            mul_assoc _ _ _
          _ = star (j ^ 2) * (star ((j ^ 2)⁻¹) * Bw) := by
            rw [hstarInv]
""",
        "FunctionalAnalysis prove star preservation of inverse explicitly",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
