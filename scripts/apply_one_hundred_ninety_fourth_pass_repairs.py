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
        """  sheaf : QGaugePresheaf Open
  PrimeProfile : PrimeIndex → Type v
""",
        """  sheaf : QGaugePresheaf.{u, v} Open
  PrimeProfile : PrimeIndex → Type v
""",
        "Mock2 pin the primality sheaf value universe",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """@[simp]
theorem unitaryRaising_zero (k : ℝ) (τ : UpperHalfPlane) :
    unitaryRaising k (fun _ => 0) τ = 0 := by
  simp [unitaryRaising, partialX, partialY, realDifferential,
    localExtension]

@[simp]
theorem unitaryLowering_zero (k : ℝ) (τ : UpperHalfPlane) :
    unitaryLowering k (fun _ => 0) τ = 0 := by
  simp [unitaryLowering, partialX, partialY, realDifferential,
    localExtension]
""",
        """@[simp]
theorem unitaryRaising_zero (k : ℝ) (τ : UpperHalfPlane) :
    unitaryRaising k (fun _ => 0) τ = 0 := by
  have hzero :
      fderiv ℝ (localExtension (fun _ : UpperHalfPlane => (0 : ℂ)))
        (τ : ℂ) = 0 := by
    have hfun : localExtension (fun _ : UpperHalfPlane => (0 : ℂ)) =
        fun _ : ℂ => (0 : ℂ) := by
      rfl
    rw [hfun]
    simp
  unfold unitaryRaising partialX partialY realDifferential
  rw [hzero]
  simp

@[simp]
theorem unitaryLowering_zero (k : ℝ) (τ : UpperHalfPlane) :
    unitaryLowering k (fun _ => 0) τ = 0 := by
  have hzero :
      fderiv ℝ (localExtension (fun _ : UpperHalfPlane => (0 : ℂ)))
        (τ : ℂ) = 0 := by
    have hfun : localExtension (fun _ : UpperHalfPlane => (0 : ℂ)) =
        fun _ : ℂ => (0 : ℂ) := by
      rfl
    rw [hfun]
    simp
  unfold unitaryLowering partialX partialY realDifferential
  rw [hzero]
  simp
""",
        "Mock2 Advanced prove the zero Maass operators from the constant derivative",
    )
    m2a = replace_exact(
        m2a,
        """theorem sinh_le_half_exp (x : ℝ) :
    Real.sinh x ≤ Real.exp x / 2 := by
  change (Real.exp x - Real.exp (-x)) / 2 ≤ Real.exp x / 2
  linarith [Real.exp_pos (-x)]
""",
        """theorem sinh_le_half_exp (x : ℝ) :
    Real.sinh x ≤ Real.exp x / 2 := by
  have hsinh :
      Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 := by
    apply Complex.ofReal_injective
    simp [Real.sinh, Complex.sinh]
  rw [hsinh]
  linarith [Real.exp_pos (-x)]
""",
        "Mock2 Advanced expose the real hyperbolic-sine exponential formula",
    )
    m2a = replace_exact(
        m2a,
        """theorem not_summable_criticalModulusEnvelope
    {A : ℝ} (hA : A ≠ 0) :
    ¬ Summable (criticalModulusEnvelope A) := by
  simpa only [criticalModulusEnvelope, sub_zero] using
    (CorrectedLemmas.KloostermanTail.not_summable_nonzero_mul_paper_tail_one
      (A := A) (ε := 0) hA (le_refl 0))
""",
        """theorem not_summable_criticalModulusEnvelope
    {A : ℝ} (hA : A ≠ 0) :
    ¬ Summable (criticalModulusEnvelope A) := by
  change ¬ Summable
    (fun n : ℕ => A * (1 / |(n : ℝ) + 1| ^ (1 : ℝ)))
  simpa only [add_zero] using
    (CorrectedLemmas.KloostermanTail.not_summable_nonzero_mul_paper_tail_one
      (A := A) (ε := 0) hA (le_refl 0))
""",
        "Mock2 Advanced align the critical modulus envelope definitionally",
    )
    m2a = replace_exact(
        m2a,
        """  filter_upwards [hdom, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hupper := hC x hx1
  have hlower : C * x ^ (1 / 4 : ℝ) < x ^ (1 / 2 : ℝ) := by
    simpa only [one_mul] using hx
  exact (not_lt_of_ge hupper) hlower
""",
        """  obtain ⟨x, hx, hx1⟩ :=
    (hdom.and (eventually_ge_atTop (1 : ℝ))).exists
  have hupper := hC x hx1
  have hlower : C * x ^ (1 / 4 : ℝ) < x ^ (1 / 2 : ℝ) := by
    simpa only [one_mul] using hx
  exact (not_lt_of_ge hupper) hlower
""",
        "Mock2 Advanced extract a concrete atTop contradiction witness",
    )
    m2a = replace_exact(
        m2a,
        """theorem positiveModulus_cast_pos (c : ℕ) :
    0 < (positiveModulus c : ℝ) := by
  exact_mod_cast positiveModulus_pos c
""",
        """theorem positiveModulus_cast_pos (c : ℕ) :
    0 < (positiveModulus c : ℝ) := by
  exact_mod_cast positiveModulus_pos c

instance positiveModulus_neZero (c : ℕ) : NeZero (positiveModulus c) :=
  ⟨Nat.ne_of_gt (positiveModulus_pos c)⟩
""",
        "Mock2 Advanced install positivity of every shifted modulus",
    )
    m2a = replace_exact(
        m2a,
        "∑ c in",
        "∑ c ∈",
        "Mock2 Advanced use the current finite-sum binder syntax",
        expected=7,
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hdet : g.det = 1 := by
    simp [g]
  have hg : 0 < g.det.val := by
    simp [hdet]
  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, g, hdet, one_div] using
""",
        """  have hdet : g.val.det = 1 := by
    simp [g]
  have hg : 0 < g.det.val := by
    simpa only [hdet] using (show (0 : ℝ) < 1 by norm_num)
  simpa [gammaTwoMoebiusChart, gammaTwoMoebiusCoordinate,
    inverseEtaPaperOrbitDenom, g, hdet, one_div] using
""",
        "FunctionalAnalysis normalize the underlying real matrix determinant",
    )
    fa = replace_exact(
        fa,
        """    simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, hg,
      inverseEtaPaperOrbitDenom, inverseEtaPaperOrbit_det_eq_one,
      g, smul_eq_mul]
""",
        """    simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, hg,
      inverseEtaPaperOrbitDenom, inverseEtaPaperOrbit_det_eq_one,
      g, smul_eq_mul, mul_comm]
""",
        "FunctionalAnalysis commute the scalar derivative coefficient",
    )
    fa = replace_exact(
        fa,
        """    simpa [G, g,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      (RealSmooth.contDiffAt_upperLift hf
        (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z)).
          differentiableAt (by simp)
""",
        """    simpa [G, g,
      GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      ((RealSmooth.contDiffAt_upperLift hf
        (((γ : GammaTwoQuotientGeometry.GammaTwo) : SL(2, ℤ)) • z)).
          differentiableAt (by simp))
""",
        "FunctionalAnalysis parenthesize the outer differentiability proof",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
