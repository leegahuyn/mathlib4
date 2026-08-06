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
    (n := minSmoothness ℂ 3) (m := ∞) le_top
""",
        """noncomputable local instance gaugeLieGroupMinSmoothness :
    LieGroup I_G (minSmoothness ℂ 3) G :=
  LieGroup.of_le (I := I_G) (G := G)
    (m := minSmoothness ℂ 3) (n := ∞) le_top
""",
        "Mock2 correct the target/source order for LieGroup.of_le",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """  have hbase : g • τ ∈ frontier s := by
    have hpre :
        τ ∈ (fun w : UpperHalfPlane => g • w) ⁻¹' frontier s := by
      rw [(Homeomorph.smul g).preimage_frontier s]
      exact hτfrontier
    exact hpre
""",
        """  have hbase : g • τ ∈ frontier s := by
    have hfrontier :
        frontier ((fun w : UpperHalfPlane => g • w) ⁻¹' s) =
          (fun w : UpperHalfPlane => g • w) ⁻¹' frontier s := by
      simpa only [realGL_smul] using
        (Homeomorph.smul (realGL g)).preimage_frontier s
    exact hfrontier ▸ hτfrontier
""",
        "Mock2 Advanced transport frontier through the actual GL homeomorphism",
    )
    m2a = replace_exact(
        m2a,
        """  have hbase : repMatrix r • τ ∈ frontier ModularGroup.fd := by
    have hpre :
        τ ∈ (fun w : UpperHalfPlane => repMatrix r • w) ⁻¹'
          frontier ModularGroup.fd := by
      rw [(Homeomorph.smul (repMatrix r)).preimage_frontier ModularGroup.fd]
      exact hτfrontier
    exact hpre
""",
        """  have hbase : repMatrix r • τ ∈ frontier ModularGroup.fd := by
    have hfrontier :
        frontier
            ((fun w : UpperHalfPlane => repMatrix r • w) ⁻¹'
              ModularGroup.fd) =
          (fun w : UpperHalfPlane => repMatrix r • w) ⁻¹'
            frontier ModularGroup.fd := by
      simpa only [realGL_smul] using
        (Homeomorph.smul (realGL (repMatrix r))).preimage_frontier
          ModularGroup.fd
    have hclosed :
        τ ∈ frontier
          ((fun w : UpperHalfPlane => repMatrix r • w) ⁻¹'
            ModularGroup.fd) := by
      simpa [closedCell] using hτfrontier
    exact hfrontier ▸ hclosed
""",
        "Mock2 Advanced transport closed-cell frontier through realGL",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  simpa [rpowScale, Function.comp_def] using
    Complex.ofRealCLM.contDiff.contDiffAt.comp w hp
""",
        """  change ContDiffAt ℝ ∞
    (fun z : ℂ => ((z.im ^ p : ℝ) : ℂ)) w
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp w hp
""",
        "FunctionalAnalysis expose rpowScale in the smoothness proof",
    )
    fa = replace_exact(
        fa,
        """  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L ξ) hc.fderiv
  simpa [rpowScale, Function.comp_def,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.imCLM_apply, smul_eq_mul, mul_assoc] using h
""",
        """  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L ξ) hc.fderiv
  change fderiv ℝ (fun z : ℂ => ((z.im ^ p : ℝ) : ℂ)) w ξ = _
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Complex.imCLM_apply, smul_eq_mul,
    mul_assoc] using h
""",
        "FunctionalAnalysis expose rpowScale in the derivative formula",
    )
    fa = replace_exact(
        fa,
        """  rw [fderiv_mul
    (rpowScale_contDiffAt_of_im_pos p hw).differentiableAt (by simp)
    ((u.contDiff.differentiable (by simp)) w)]
""",
        """  have hscale : DifferentiableAt ℝ (rpowScale p) w :=
    (rpowScale_contDiffAt_of_im_pos p hw).differentiableAt (by simp)
  have hu : DifferentiableAt ℝ (u : ℂ → ℂ) w :=
    (u.contDiff.differentiable (by simp)) w
  rw [fderiv_mul hscale hu]
""",
        "FunctionalAnalysis make the product-rule differentiability proofs explicit",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
