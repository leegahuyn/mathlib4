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
    m2 = replace_exact(
        m2,
        "structure Proposition15FunctorBridgeCertificate : Prop where",
        "structure Proposition15FunctorBridgeCertificate where",
        "Mock2 make the Proposition 15 certificate data-valued",
    )
    m2 = replace_exact(
        m2,
        "theorem proposition15_functorBridge_certificate :",
        "noncomputable def proposition15_functorBridge_certificate :",
        "Mock2 define rather than prove the data-valued Proposition 15 certificate",
    )
    m2 = replace_exact(
        m2,
        """def quotientMap (τ : H) : X :=
  Quotient.mk' τ
""",
        """def quotientMap (τ : H) : X :=
  Definition11.quotientMk τ
""",
        "Mock2 reuse the explicit orbit quotient projection",
    )
    m2 = replace_exact(
        m2,
        """@[simp] theorem quotientMap_smul (γ : Gamma2) (τ : H) :
    quotientMap (γ • τ) = quotientMap τ := by
  change Definition11.quotientMk (γ • τ) = Definition11.quotientMk τ
  exact Definition11.quotientMk_smul γ τ
""",
        """@[simp] theorem quotientMap_smul (γ : Gamma2) (τ : H) :
    quotientMap (γ • τ) = quotientMap τ := by
  simpa only [quotientMap] using Definition11.quotientMk_smul γ τ
""",
        "Mock2 prove quotient invariance through the reused projection",
    )
    m2 = replace_exact(
        m2,
        """def quotientMapContinuous : C(H, X) where
  toFun := quotientMap
  continuous_toFun := continuous_quotient_mk'
""",
        """def quotientMapContinuous : C(H, X) where
  toFun := quotientMap
  continuous_toFun := by
    simpa only [quotientMap, Definition11.quotientMk] using
      (continuous_quot_mk :
        Continuous (@Quot.mk H (MulAction.orbitRel Gamma2 H).r))
""",
        "Mock2 bundle continuity of the explicit Quot projection",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        "    simpa [Real.sinh, ← Complex.ofReal_neg] using h\n",
        "    simpa only [Complex.sinh_ofReal_re, Complex.exp_ofReal_re] using h\n",
        "Mock2 Advanced normalize real parts of complex sinh and exp",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  simpa [W, firstDerivative, div_eq_mul_inv, mul_comm] using
    ((hasDerivAt_id x).neg.div_const 2).exp
""",
        """theorem hasDerivAt_W (x : ℝ) :
    HasDerivAt W (firstDerivative x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => -y / 2) (-(1 : ℝ) / 2) x := by
    convert ((hasDerivAt_id x).neg.div_const 2) using 1 <;> ring
  simpa [W, firstDerivative, mul_comm] using hinner.exp
""",
        "Mock2 Advanced name the exact Whittaker inner derivative",
    )
    m2a = replace_exact(
        m2a,
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  unfold firstDerivative secondDerivative
  convert (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2) using 1
  ring
""",
        """theorem hasDerivAt_firstDerivative (x : ℝ) :
    HasDerivAt firstDerivative (secondDerivative x) x := by
  have hcoeff :
      secondDerivative x = (-(1 : ℝ) / 2) * firstDerivative x := by
    simp [firstDerivative, secondDerivative]
    ring
  rw [hcoeff]
  simpa only [firstDerivative] using
    (hasDerivAt_W x).const_mul (-(1 : ℝ) / 2)
""",
        "Mock2 Advanced separate the second-derivative coefficient identity",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, g, hdet, one_div] using
    (UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg z)
""",
        """  have hdetC : (g.val.det : ℂ) = 1 := by
    exact_mod_cast hdet
  have hraw := UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg z
  rw [hdetC] at hraw
  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, g, one_div] using hraw
""",
        "FunctionalAnalysis normalize the Möbius derivative numerator after casting",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
