from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
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
        """noncomputable local instance gaugeLieGroupMinSmoothness :
    LieGroup I_G (minSmoothness ℂ 3) G :=
  LieGroup.of_le (I := I_G) (G := G)
    (m := minSmoothness ℂ 3) (n := ∞) le_top
""",
        """noncomputable local instance gaugeLieGroupMinSmoothness :
    LieGroup I_G (minSmoothness ℂ 3) G := by
  simpa using (inferInstance : LieGroup I_G (3 : ℕ∞ω) G)
""",
        "Mock2 derive complex minSmoothness from the finite LieGroup instance",
    )
    M2.write_text(m2, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  rw [fderiv_mul
    ((rpowScale_contDiffAt_of_im_pos p hw).differentiableAt (by simp))
    ((u.contDiff.differentiable (by simp)) w)]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_rpowScale_apply_of_im_pos p hw]
  simp only [directionalDerivative_apply]
""",
        """  change (fderiv ℝ (rpowScale p * (u : ℂ → ℂ)) w) ξ = _
  rw [fderiv_mul
    ((rpowScale_contDiffAt_of_im_pos p hw).differentiableAt (by simp))
    ((u.contDiff.differentiable (by simp)) w)]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_rpowScale_apply_of_im_pos p hw]
  simp only [directionalDerivative_apply]
  ring
""",
        "FunctionalAnalysis normalize the weighted product derivative",
    )
    fa = replace_exact(
        fa,
        """theorem compactPair_directionalDerivative_left
    (ξ : ℂ) (u v : Core) :
    compactPair (directionalDerivative ξ u) v =
      -compactPair u (directionalDerivative ξ v) := by
  have h := compactPair_directionalDerivative_right ξ u v
  linear_combination -h
""",
        """theorem compactPair_directionalDerivative_left
    (ξ : ℂ) (u v : Core) :
    compactPair (directionalDerivative ξ u) v =
      -compactPair u (directionalDerivative ξ v) := by
  have h := compactPair_directionalDerivative_right ξ u v
  rw [h]
  simp
""",
        "FunctionalAnalysis orient the compact-pair identity directly",
    )
    fa = replace_exact(
        fa,
        """    · exact (hf w hw).contDiffAt.mul v.contDiff.contDiffAt
""",
        """    · exact ((hf w hw).contDiffAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).mul
        v.contDiff.contDiffAt
""",
        "FunctionalAnalysis discharge the upper-half-plane neighborhood before multiplication",
    )
    fa = replace_exact(
        fa,
        """  change fderiv ℝ (fun w : ℂ => upperLift f w * v w) (z : ℂ) ξ = _
  rw [fderiv_mul
    (RealSmooth.contDiffAt_upperLift hf z).differentiableAt (by simp)
    ((v.contDiff.differentiable (by simp)) (z : ℂ))]
""",
        """  change (fderiv ℝ (upperLift f * (v : ℂ → ℂ)) (z : ℂ)) ξ = _
  rw [fderiv_mul
    ((RealSmooth.contDiffAt_upperLift hf z).differentiableAt (by simp))
    ((v.contDiff.differentiable (by simp)) (z : ℂ))]
""",
        "FunctionalAnalysis expose the localized product before fderiv_mul",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
