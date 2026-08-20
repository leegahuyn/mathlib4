from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def replace_in_block(text: str, start: str, end: str, old: str, new: str,
                     expected: int, label: str) -> str:
    i = text.index(start)
    j = text.index(end, i)
    block = text[i:j]
    count = block.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    block = block.replace(old, new)
    print(f"{label}: applied {count}")
    return text[:i] + block + text[j:]


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """@[simp] theorem leftLogarithmicDerivativeValue_constant (U : Opens)
    (a : G) (τ : coverOpen U) :
    leftLogarithmicDerivativeValue I_G G
      (SmoothGaugeMap.constant I_G G U a) τ = 0 := by
  simp [leftLogarithmicDerivativeValue, mfderiv_const]
""",
        """@[simp] theorem leftLogarithmicDerivativeValue_constant (U : Opens)
    (a : G) (τ : coverOpen U) :
    leftLogarithmicDerivativeValue I_G G
      (SmoothGaugeMap.constant I_G G U a) τ = 0 := by
  change
    (mfderiv I_G I_G (fun x : G => a⁻¹ * x) a).comp
      (mfderiv 𝓘(ℂ) I_G (fun _ : coverOpen U => a) τ) = 0
  rw [mfderiv_const]
  exact ContinuousLinearMap.comp_zero _
""",
        "Mock2 reduce the constant Maurer-Cartan derivative explicitly",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """attribute [-instance] Complex.instField

/-- Exact tangent formula for the cusp at zero. -/
""",
        """attribute [-instance] Complex.instField
attribute [-instance] Complex.instDenselyNormedField

/-- Exact tangent formula for the cusp at zero. -/
""",
        "Mock2 Advanced remove the nontrivially normed field diamond",
    )
    m2a = replace_exact(
        m2a,
        """      (cuspFiniteAmbientTangent Y x) x := by
  have hreal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt (x := x)).hasDerivAt
  have hneg :
      HasDerivAt (fun t : ℝ => -cuspHorizontalAmbientCurve Y t) (-1) x := by
    change HasDerivAt
      (fun t : ℝ => -((t : ℂ) + (Y : ℂ) * Complex.I)) (-1) x
    exact (hreal.add_const ((Y : ℂ) * Complex.I)).neg
  have hne : -cuspHorizontalAmbientCurve Y x ≠ 0 :=
    neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        """      (cuspFiniteAmbientTangent Y x) x := by
  have hneg :
      HasDerivAt (fun t : ℝ => -cuspHorizontalAmbientCurve Y t) (-1) x :=
    (hasDerivAt_cuspHorizontalAmbientCurve Y x).neg
  have hne : -cuspHorizontalAmbientCurve Y x ≠ 0 :=
    neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        "Mock2 Advanced reuse the established horizontal derivative after removing the diamond",
    )
    m2a = replace_exact(
        m2a,
        """attribute [instance] Complex.instField
attribute [instance] Complex.instRing
""",
        """attribute [instance] Complex.instDenselyNormedField
attribute [instance] Complex.instField
attribute [instance] Complex.instRing
""",
        "Mock2 Advanced restore the dense complex field",
    )
    m2a = replace_exact(
        m2a,
        """      calc
        ModularGroup.S • g = ModularGroup.S * g := rfl
        _ = ModularGroup.S * (repMatrix r * h) := by rw [hg]
        _ = (ModularGroup.S * repMatrix r) * h := by rw [mul_assoc]
        _ = (repMatrix r' * k) * h := by rw [htransition]
        _ = repMatrix r' * (k * h) := by rw [mul_assoc]
""",
        """      change ModularGroup.S * g = repMatrix r' * (k * h)
      rw [hg, mul_assoc, htransition, mul_assoc]
""",
        "Mock2 Advanced expose the S action as matrix multiplication",
    )
    m2a = replace_exact(
        m2a,
        """      calc
        ModularGroup.T • g = ModularGroup.T * g := rfl
        _ = ModularGroup.T * (repMatrix r * h) := by rw [hg]
        _ = (ModularGroup.T * repMatrix r) * h := by rw [mul_assoc]
        _ = (repMatrix r' * k) * h := by rw [htransition]
        _ = repMatrix r' * (k * h) := by rw [mul_assoc]
""",
        """      change ModularGroup.T * g = repMatrix r' * (k * h)
      rw [hg, mul_assoc, htransition, mul_assoc]
""",
        "Mock2 Advanced expose the T action as matrix multiplication",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  simpa [M, F, Complex.ofReal_mul,
    Complex.normSq_eq_conj_mul_self] using hScaleC
""",
        """  simpa [M, F, Complex.ofReal_mul, starRingEnd_apply,
    Complex.normSq_eq_conj_mul_self] using hScaleC
""",
        "FunctionalAnalysis normalize starRingEnd in source fiber cancellation",
    )
    fa = replace_exact(
        fa,
        """    simpa only [Complex.ofReal_mul,
      Complex.normSq_eq_conj_mul_self] using hScaleC
""",
        """    simpa only [Complex.ofReal_mul, starRingEnd_apply,
      Complex.normSq_eq_conj_mul_self] using hScaleC
""",
        "FunctionalAnalysis normalize starRingEnd in Green covariance",
    )
    fa = replace_exact(
        fa,
        """  rw [fixedPhaseGreenScalarDensity, hu', hv', map_mul]
""",
        """  rw [fixedPhaseGreenScalarDensity, hu', hv', star_mul]
""",
        "FunctionalAnalysis expand star over the fixed-phase product",
    )
    fa = replace_exact(
        fa,
        """          (v : SmoothQuotientCompactFunction) z := by ring
""",
        """          (v : SmoothQuotientCompactFunction) z) := by ring
""",
        "FunctionalAnalysis close the first Green covariance calc expression",
    )
    fa = replace_in_block(
        fa,
        "namespace FixedPhasePeterssonCoordinates",
        "end FixedPhasePeterssonCoordinates",
        "RealSmooth",
        "SmoothCompactCoreGeometry.RealSmooth",
        15,
        "FunctionalAnalysis qualify fixed-phase real smoothness",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
