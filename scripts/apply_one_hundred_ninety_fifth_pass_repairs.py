from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    start = m2.index("structure Proposition15FunctorBridgeCertificate : Prop where")
    end = m2.index("theorem proposition15_functorBridge_certificate", start)
    segment = m2[start:end]
    old = "BalancedQGaugeSheafCategory Open"
    expected = 11
    count = segment.count(old)
    if count != expected:
        raise RuntimeError(
            f"Mock2 pin Proposition 15 source universes: expected {expected}, found {count}"
        )
    print(f"Mock2 pin Proposition 15 source universes: applied {expected}")
    segment = segment.replace(old, "BalancedQGaugeSheafCategory.{u, v} Open")
    m2 = m2[:start] + segment + m2[end:]
    m2 = replace_exact(
        m2,
        """    Proposition15FunctorBridgeCertificate (Open := Open) := by
""",
        """    Proposition15FunctorBridgeCertificate.{u, v} (Open := Open) := by
""",
        "Mock2 instantiate the Proposition 15 certificate universes",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem sinh_le_half_exp (x : ℝ) :
    Real.sinh x ≤ Real.exp x / 2 := by
  have hsinh :
      Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 := by
    apply Complex.ofReal_injective
    simp [Real.sinh, Complex.sinh]
  rw [hsinh]
  linarith [Real.exp_pos (-x)]
""",
        """theorem sinh_le_half_exp (x : ℝ) :
    Real.sinh x ≤ Real.exp x / 2 := by
  have hsinh :
      2 * Real.sinh x = Real.exp x - Real.exp (-x) := by
    have h := congrArg Complex.re (Complex.two_sinh (x : ℂ))
    simpa [Real.sinh, ← Complex.ofReal_neg] using h
  linarith [Real.exp_pos (-x)]
""",
        "Mock2 Advanced derive the real sinh identity from Complex.two_sinh",
    )
    m2a = replace_exact(
        m2a,
        """  simpa only [add_zero] using
    (CorrectedLemmas.KloostermanTail.not_summable_nonzero_mul_paper_tail_one
""",
        """  simpa only [sub_zero] using
    (CorrectedLemmas.KloostermanTail.not_summable_nonzero_mul_paper_tail_one
""",
        "Mock2 Advanced normalize the critical exponent subtraction",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  unfold W firstDerivative
  convert ((hasDerivAt_id x).neg.div_const 2).exp using 1 <;> ring
""",
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  simpa [W, firstDerivative, div_eq_mul_inv, mul_comm] using
    ((hasDerivAt_id x).neg.div_const 2).exp
""",
        "Mock2 Advanced normalize the half-order Whittaker derivative",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  unfold firstDerivative secondDerivative
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1 <;>
    simp only [firstDerivative] <;> ring
""",
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  unfold firstDerivative secondDerivative
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  ring
""",
        "Mock2 Advanced normalize the second Whittaker derivative",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hdet : g.val.det = 1 := by
    simp [g]
  have hg : 0 < g.det.val := by
    simpa only [hdet] using (show (0 : ℝ) < 1 by norm_num)
""",
        """  have hdet : g.val.det = 1 := by
    simpa [g] using inverseEtaPaperOrbit_det_eq_one γ
  have hg : 0 < g.det.val := by
    simpa [g] using inverseEtaPaperOrbit_det_pos γ
""",
        "FunctionalAnalysis reuse the established determinant identities",
    )
    fa = replace_exact(
        fa,
        """  have hOuter : DifferentiableAt ℝ (upperLift f) (G (z : ℂ)) := by
    simpa [G, g,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      ((RealSmooth.contDiffAt_upperLift hf
        (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z)).
          differentiableAt (by simp))
""",
        """  have hOuter : DifferentiableAt ℝ (upperLift f) (G (z : ℂ)) := by
    have hSmooth := RealSmooth.contDiffAt_upperLift hf
      (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z)
    simpa [G, g,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      hSmooth.differentiableAt (by simp)
""",
        "FunctionalAnalysis name the outer smoothness proof before differentiation",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
