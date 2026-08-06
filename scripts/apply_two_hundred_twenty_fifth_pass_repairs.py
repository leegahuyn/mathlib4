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
        """noncomputable local instance gaugeLieGroupMinSmoothness :
    LieGroup I_G (minSmoothness ℂ 3) G :=
  LieGroup.of_le (I := I_G) (G := G)
    (show minSmoothness ℂ 3 ≤ (∞ : ℕ∞ω) from le_top)
""",
        """noncomputable local instance gaugeLieGroupMinSmoothness :
    LieGroup I_G (minSmoothness ℂ 3) G :=
  LieGroup.of_le (I := I_G) (G := G)
    (by simp [minSmoothness] :
      minSmoothness ℂ 3 ≤ (∞ : ℕ∞ω))
""",
        "Mock2 prove complex minSmoothness is below C-infinity",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹' frontier s := by
      rw [(Homeomorph.smul gR).preimage_frontier s]
      simpa [gR, realGL_smul] using hτfrontier
""",
        """    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹' frontier s := by
      change τ ∈ ⇑(Homeomorph.smul gR) ⁻¹' frontier s
      rw [(Homeomorph.smul gR).preimage_frontier s]
      change τ ∈ frontier ((fun w : UpperHalfPlane => gR • w) ⁻¹' s)
      simpa [gR, realGL_smul] using hτfrontier
""",
        "Mock2_Advanced normalize both sides of frontier pullback",
    )
    m2a = replace_exact(
        m2a,
        """    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹'
          frontier ModularGroup.fd := by
      rw [(Homeomorph.smul gR).preimage_frontier ModularGroup.fd]
      simpa [gR, realGL_smul] using hτfrontier
""",
        """    have hpre :
        τ ∈ (fun w : UpperHalfPlane => gR • w) ⁻¹'
          frontier ModularGroup.fd := by
      change τ ∈ ⇑(Homeomorph.smul gR) ⁻¹' frontier ModularGroup.fd
      rw [(Homeomorph.smul gR).preimage_frontier ModularGroup.fd]
      change τ ∈ frontier
        ((fun w : UpperHalfPlane => gR • w) ⁻¹' ModularGroup.fd)
      have hclosed :
          τ ∈ frontier
            ((fun w : UpperHalfPlane => repMatrix r • w) ⁻¹'
              ModularGroup.fd) := by
        simpa [closedCell] using hτfrontier
      simpa [gR, realGL_smul] using hclosed
""",
        "Mock2_Advanced normalize the closed-cell frontier pullback",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  change fderiv ℝ
    (fun z : ℂ => rpowScale p z * (u : ℂ → ℂ) z) w ξ = _
  change (fderiv ℝ (rpowScale p * (u : ℂ → ℂ)) w) ξ = _
  rw [fderiv_mul
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
        "FunctionalAnalysis close the weighted product rule by commutativity",
    )
    fa = replace_exact(
        fa,
        """    · exact (hf w hw).contDiffAt.mul v.contDiff.contDiffAt
""",
        """    · exact
        (RealSmooth.contDiffAt_upperLift hf ⟨w, hw⟩).mul
          v.contDiff.contDiffAt
""",
        "FunctionalAnalysis use upper-lift smoothness at an interior point",
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
        "FunctionalAnalysis expose localization multiplication before differentiation",
    )
    fa = replace_exact(
        fa,
        """    (by simpa only [one_mul, directionalDerivative_apply] using
      core_integrable (directionalDerivative ξ u))
""",
        """    (by
      exact (core_integrable (directionalDerivative ξ u)).congr
        (Filter.Eventually.of_forall fun x =>
          directionalDerivative_apply ξ u x))
""",
        "FunctionalAnalysis transport derivative integrability pointwise",
    )
    fa = replace_exact(
        fa,
        """  simpa only [one_mul, zero_mul, integral_zero, neg_zero,
    directionalDerivative_apply] using h
""",
        """  simpa only [one_mul, fderiv_const, zero_apply, zero_mul,
    integral_zero, neg_zero, directionalDerivative_apply] using h
""",
        "FunctionalAnalysis reduce the derivative of the constant test function",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
