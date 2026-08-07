from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "b08f67384828a0bbbd8621552a7feb92462271eaba83b2db6eaa4eaf8f7c8f1f"
EXPECTED_OUTPUT_SHA256 = "97bd40b0149364544c1fecb1a835c77b6190ebd66f141f8a9f3abc94ac84d977"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    print(f"{label}: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass344] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass344 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_once(
        text,
        '''  simp only [raiseCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply, Pi.sub_apply]
  change
    raiseRaw (paperOrbitExponent n)
        (upstairsCuspCutoff N *
          (u : SmoothQuotientCompactFunction)) z -
      upstairsCuspCutoff N z *
        raiseRaw (paperOrbitExponent n)
          (u : SmoothQuotientCompactFunction) z = _
  rw [raiseRaw_mul_cutoff (upstairsCuspCutoff_realSmooth N)
    (u : SmoothQuotientCompactFunction).1.2]
  ring
''',
        '''  simp only [raiseCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]
  change
    (((InverseEtaFixedPhaseCore.raise n)
        (cuspCutoffOperator N n u) :
          InverseEtaFixedPhaseCore (n + 1)) :
        SmoothQuotientCompactFunction) z -
      (((cuspCutoffOperator N (n + 1))
        (InverseEtaFixedPhaseCore.raise n u) :
          InverseEtaFixedPhaseCore (n + 1)) :
        SmoothQuotientCompactFunction) z = _
  simp only [InverseEtaFixedPhaseCore.raise_apply,
    cuspCutoffOperator_apply]
  rw [raiseRaw_mul_cutoff (upstairsCuspCutoff_realSmooth N)
    (u : SmoothQuotientCompactFunction).1.2]
  ring
''',
        "FunctionalAnalysis expose typed raising commutator pointwise",
    )
    text = replace_once(
        text,
        '''  simp only [lowerCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply, Pi.sub_apply]
  change
    lowerRaw (paperOrbitExponent n)
        (upstairsCuspCutoff N *
          (u : SmoothQuotientCompactFunction)) z -
      upstairsCuspCutoff N z *
        lowerRaw (paperOrbitExponent n)
          (u : SmoothQuotientCompactFunction) z = _
  rw [lowerRaw_mul_cutoff (upstairsCuspCutoff_realSmooth N)
    (u : SmoothQuotientCompactFunction).1.2]
  ring
''',
        '''  simp only [lowerCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply]
  change
    (((InverseEtaFixedPhaseCore.lower n)
        (cuspCutoffOperator N n u) :
          InverseEtaFixedPhaseCore (n - 1)) :
        SmoothQuotientCompactFunction) z -
      (((cuspCutoffOperator N (n - 1))
        (InverseEtaFixedPhaseCore.lower n u) :
          InverseEtaFixedPhaseCore (n - 1)) :
        SmoothQuotientCompactFunction) z = _
  simp only [InverseEtaFixedPhaseCore.lower_apply,
    cuspCutoffOperator_apply]
  rw [lowerRaw_mul_cutoff (upstairsCuspCutoff_realSmooth N)
    (u : SmoothQuotientCompactFunction).1.2]
  ring
''',
        "FunctionalAnalysis expose typed lowering commutator pointwise",
    )
    text = replace_once(
        text,
        '''theorem hyperbolicDensity_measurable :
    Measurable hyperbolicDensity :=
  hyperbolicDensity_continuous.measurable

theorem hyperbolicMeasure_eq_euclidean_withDensity :
''',
        '''theorem hyperbolicDensity_measurable :
    Measurable hyperbolicDensity :=
  hyperbolicDensity_continuous.measurable

@[simp]
theorem hyperbolicDensity_coe (z : ℍ) :
    (hyperbolicDensity z : ℝ) = (1 / z.im) ^ 2 := by
  simp [hyperbolicDensity]

theorem hyperbolicMeasure_eq_euclidean_withDensity :
''',
        "FunctionalAnalysis add real coercion of hyperbolic density",
    )
    text = replace_once(
        text,
        '''    _ = (hyperbolicDensity z : ℝ) *
        z.im ^ (((paperOrbitExponent n : ℤ) : ℝ) / 2) := by
      simp only [hyperbolicDensity, NNReal.coe_pow, NNReal.coe_div,
        NNReal.coe_one, NNReal.coe_mk]
''',
        '''    _ = (hyperbolicDensity z : ℝ) *
        z.im ^ (((paperOrbitExponent n : ℤ) : ℝ) / 2) := by
      rw [hyperbolicDensity_coe]
''',
        "FunctionalAnalysis close Euclidean gauge scale by density coercion",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass344 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass344] FunctionalAnalysis commutator and hyperbolic-density roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
