from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / 'PrimalitySheafVerification' / 'Mock2_FunctionalAnalysis.lean'
EXPECTED_INPUT_SHA256 = 'be21e702089c0de8f9a5a4e5c1af8eb0963869cf93271c469d0516e55caa6fd5'
EXPECTED_OUTPUT_SHA256 = 'c980501c4a7f0f6582c5d67ec7fa08c7af37ffd6aa3335a3724928f94c2de03f'


def digest(text: str) -> str:
    return sha256(text.encode('utf-8')).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise RuntimeError(f'{label}: expected {expected}, found {count}')
    return text.replace(old, new)


def main() -> None:
    text = TARGET.read_text(encoding='utf-8')
    got = digest(text)
    print(f'input_sha256={got}')
    if got == EXPECTED_OUTPUT_SHA256:
        print('[pass347] already applied')
        return
    if got != EXPECTED_INPUT_SHA256:
        raise RuntimeError(f'unexpected input hash {got}')

    text = replace_exact(text, '''noncomputable def coordinates (n : ℤ) :
    QuotientHilbertCoordinates
      (InverseEtaFixedPhaseCore n)
      (OrbitPeterssonHilbert n)
      (OrbitPeterssonHilbert (n + 1))
      (OrbitPeterssonHilbert (n - 1)) where
  base := l2Coordinate n
  raised := raisedCoordinate n
  lowered := loweredCoordinate n''', '''noncomputable def coordinates (n : ℤ) := by
  letI : AddCommGroup (InverseEtaFixedPhaseCore n) :=
    inverseEtaFixedPhaseCoreAddCommGroup n
  letI : Module ℂ (InverseEtaFixedPhaseCore n) :=
    inverseEtaFixedPhaseCoreModule n
  exact QuotientHilbertCoordinates.mk
    (l2Coordinate n) (raisedCoordinate n) (loweredCoordinate n)''',
        'infer fixed-phase coordinate structure under coherent instances')

    text = replace_exact(text, '''theorem compactInverseEtaOrbitZeroSmoothQuotient_covariant :
    IsInverseEtaPaperOrbitCovariant 0
      compactInverseEtaOrbitZeroSmoothQuotient := by
  intro γ z
  have hCov :=
    SmoothCompactWeightCore.covariance
      compactInverseEtaOrbitZeroWeightCore γ z
  simpa only [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using hCov''', '''theorem compactInverseEtaOrbitZeroSmoothQuotient_covariant :
    IsInverseEtaPaperOrbitCovariant 0
      compactInverseEtaOrbitZeroSmoothQuotient := by
  intro γ z
  have hCov :=
    SmoothCompactWeightCore.covariance
      compactInverseEtaOrbitZeroWeightCore γ z
  have hAction :
      γ • z = ((γ : SL(2, ℤ)) • z) := by
    simpa [GammaTwoQuotientGeometry.gammaTwoToSL2Real] using
      (GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul γ z)
  rw [← hAction]
  simpa only [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor] using hCov''',
        'transport orbit-zero covariance to the integral action')

    text = replace_exact(text, '''theorem constantCompactCuspTail_tail_norm_eq_zero
    (C : ContinuousSesquilinearForm H) (hC : IsCompactOperator C) (n : ℕ) :
    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  apply norm_eq_zero.mpr
  exact constantCompactCuspTail_tail_eq_zero C hC n''', '''theorem constantCompactCuspTail_tail_norm_eq_zero
    (C : ContinuousSesquilinearForm H) (hC : IsCompactOperator C) (n : ℕ) :
    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  rw [constantCompactCuspTail_tail_eq_zero, norm_zero]''',
        'rewrite the exact compact tail before taking its norm')

    text = replace_exact(text, '''theorem rawOfSmoothCompactWeightCore_covariant (n : ℤ)
    (u : SmoothCompactWeightCore (OrbitMultiplier n)) :
    IsInverseEtaPaperOrbitCovariant n
      (rawOfSmoothCompactWeightCore n u) := by
  intro γ z
  have hCov := SmoothCompactWeightCore.covariance u γ z
  simpa only [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using hCov''', '''theorem rawOfSmoothCompactWeightCore_covariant (n : ℤ)
    (u : SmoothCompactWeightCore (OrbitMultiplier n)) :
    IsInverseEtaPaperOrbitCovariant n
      (rawOfSmoothCompactWeightCore n u) := by
  intro γ z
  have hCov := SmoothCompactWeightCore.covariance u γ z
  have hAction :
      γ • z = ((γ : SL(2, ℤ)) • z) := by
    simpa [GammaTwoQuotientGeometry.gammaTwoToSL2Real] using
      (GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul γ z)
  rw [← hAction]
  simpa only [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier] using hCov''',
        'transport general covariance to the integral action')

    text = replace_exact(text, '''noncomputable def raiseCuspCutoffCommutator (N : ℕ) (n : ℤ) :
    InverseEtaFixedPhaseCore n →ₗ[ℂ]
      InverseEtaFixedPhaseCore (n + 1) :=
  (InverseEtaFixedPhaseCore.raise n).comp (cuspCutoffOperator N n) -
    (cuspCutoffOperator N (n + 1)).comp
      (InverseEtaFixedPhaseCore.raise n)''', '''noncomputable def raiseCuspCutoffCommutator (N : ℕ) (n : ℤ) :
    InverseEtaFixedPhaseCore n →ₗ[ℂ]
      InverseEtaFixedPhaseCore (n + 1) where
  toFun u :=
    InverseEtaFixedPhaseCore.raise n (cuspCutoffOperator N n u) -
      cuspCutoffOperator N (n + 1) (InverseEtaFixedPhaseCore.raise n u)
  map_add' u v := by
    simp only [map_add]
    abel
  map_smul' c u := by
    simp only [map_smul, smul_sub]''',
        'construct the raising cutoff commutator pointwise')

    text = replace_exact(text, '''noncomputable def lowerCuspCutoffCommutator (N : ℕ) (n : ℤ) :
    InverseEtaFixedPhaseCore n →ₗ[ℂ]
      InverseEtaFixedPhaseCore (n - 1) :=
  (InverseEtaFixedPhaseCore.lower n).comp (cuspCutoffOperator N n) -
    (cuspCutoffOperator N (n - 1)).comp
      (InverseEtaFixedPhaseCore.lower n)''', '''noncomputable def lowerCuspCutoffCommutator (N : ℕ) (n : ℤ) :
    InverseEtaFixedPhaseCore n →ₗ[ℂ]
      InverseEtaFixedPhaseCore (n - 1) where
  toFun u :=
    InverseEtaFixedPhaseCore.lower n (cuspCutoffOperator N n u) -
      cuspCutoffOperator N (n - 1) (InverseEtaFixedPhaseCore.lower n u)
  map_add' u v := by
    simp only [map_add]
    abel
  map_smul' c u := by
    simp only [map_smul, smul_sub]''',
        'construct the lowering cutoff commutator pointwise')

    text = replace_exact(text, '''  simp only [raiseCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply, Pi.sub_apply]''', '''  simp only [raiseCuspCutoffCommutator, Pi.sub_apply]''',
        'unfold pointwise raising commutator')
    text = replace_exact(text, '''  simp only [raiseCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]''', '''  simp only [raiseCuspCutoffCommutator]''',
        'unfold eventually-zero raising commutator')
    text = replace_exact(text, '''  simp only [lowerCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply, Pi.sub_apply]''', '''  simp only [lowerCuspCutoffCommutator, Pi.sub_apply]''',
        'unfold pointwise lowering commutator')
    text = replace_exact(text, '''  simp only [lowerCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]''', '''  simp only [lowerCuspCutoffCommutator]''',
        'unfold eventually-zero lowering commutator')

    text = replace_exact(text, '''theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  unfold hyperbolicDensity
  refine .pow (.div₀ continuous_const ?_ ?_) _
  · exact UpperHalfPlane.continuous_im.subtype_mk _
  · exact fun z => NNReal.ne_iff.mp z.im_ne_zero''', '''theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  unfold hyperbolicDensity
  exact
    (.pow (.div₀ continuous_const
      (UpperHalfPlane.continuous_im.subtype_mk _)
      (fun z => NNReal.ne_iff.mp z.im_ne_zero)) _)''',
        'use the fully typed hyperbolic density continuity proof')

    text = replace_exact(text, '''theorem hyperbolicDensity_ne_zero (z : ℍ) :
    (hyperbolicDensity z : ℝ≥0∞) ≠ 0 := by
  apply ENNReal.coe_ne_zero.mpr
  exact pow_ne_zero 2 <|
    div_ne_zero one_ne_zero
      (NNReal.ne_iff.mp z.im_ne_zero)''', '''theorem hyperbolicDensity_ne_zero (z : ℍ) :
    (hyperbolicDensity z : ℝ≥0∞) ≠ 0 := by
  apply ENNReal.coe_ne_zero.mpr
  exact pow_ne_zero 2 <|
    div_ne_zero one_ne_zero
      (show NNReal.mk z.im z.im_pos.le ≠ 0 from
        NNReal.ne_iff.mp z.im_ne_zero)''',
        'type the positive NNReal denominator explicitly')

    text = replace_exact(text, '''  have hnot : ∀ᵐ z ∂upperEuclideanMeasure,
      z ∉ chosenGammaTwoFundamentalDomain.carrier \
        gammaTwoOpenCarrier := by
    rw [ae_iff]
    simpa using chosenCarrier_diff_open_null_upperEuclidean''', '''  have hnot : ∀ᵐ z ∂upperEuclideanMeasure,
      z ∉ chosenGammaTwoFundamentalDomain.carrier \
        gammaTwoOpenCarrier := by
    rw [ae_iff]
    change upperEuclideanMeasure
      (chosenGammaTwoFundamentalDomain.carrier \
        gammaTwoOpenCarrier) = 0
    exact chosenCarrier_diff_open_null_upperEuclidean''',
        'keep the set-difference carrier definitionally aligned')

    text = replace_exact(text, '''  exact (Lp.memLp q).star.congr <|
    Filter.Eventually.of_forall fun z => by
      rw [Function.comp_apply, ambientStarRepresentative_apply]
      rfl''', '''  exact MemLp.ae_eq
    (Filter.Eventually.of_forall fun z => by
      rw [Function.comp_apply, ambientStarRepresentative_apply]
      rfl)
    (Lp.memLp q).star''',
        'transport starred Lp membership by almost-everywhere equality')

    text = replace_exact(text, '''      exact hw <| by
        rw [image_eq_zero_of_notMem_tsupport hwv, mul_zero]''', '''      exact hw <| by
        change ambientStarRepresentative n q w * v w = 0
        rw [image_eq_zero_of_notMem_tsupport hwv, mul_zero]''',
        'expose the ambient integral integrand before rewriting')

    out = digest(text)
    print(f'output_sha256={out}')
    if out != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(f'unexpected output hash {out}')
    TARGET.write_text(text, encoding='utf-8')
    print('[pass347] coordinate instances, covariance, commutators, density, and measure API repaired')


if __name__ == '__main__':
    main()
