from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "0c052ff4a58c5945188c8b9b1e736b8ac2ef57bcb293fc05aacbdc60430ee6c3"
EXPECTED_OUTPUT_SHA256 = "d9bce9ec296c799fe144786111da5a6e8f7f0232f55fd34df9cf09be8b140b4e"

REPLACEMENTS = [
    {
        "name": "graph canonical subtype instances",
        "old": """/- `InverseEtaFixedPhaseCore` is definitionally the subtype of the stable
submodule.  Use the canonical subtype additive and module instances; introducing
a second local instance family makes later linear maps definitionally
incompatible with the already-constructed core maps. -/

""",
        "new": """/- `InverseEtaFixedPhaseCore` is definitionally the subtype of the stable
submodule. Re-expose exactly the canonical subtype instances so the opaque
abbreviation elaborates while retaining definitional compatibility with the
previously constructed core maps. -/
noncomputable local instance fixedPhaseGraphCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n))

noncomputable local instance fixedPhaseGraphCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n))

""",
    },
    {
        "name": "orbit-zero covariance reverse bridge",
        "old": """  have hCov :=
    SmoothCompactWeightCore.covariance
      compactInverseEtaOrbitZeroWeightCore γ z
  simpa [compactInverseEtaOrbitZeroSmoothQuotient,
""",
        "new": """  have hCov :=
    SmoothCompactWeightCore.covariance
      compactInverseEtaOrbitZeroWeightCore γ z
  rw [← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov
  simpa [compactInverseEtaOrbitZeroSmoothQuotient,
""",
    },
    {
        "name": "constant compact-tail norm through norm_eq_zero",
        "old": """    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  simpa only [constantCompactCuspTail_tail_eq_zero, norm_zero]
""",
        "new": """    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  exact norm_eq_zero.mpr
    (constantCompactCuspTail_tail_eq_zero C hC n)
""",
    },
    {
        "name": "density canonical subtype instances",
        "old": """/- Keep the canonical subtype instances inherited from
`inverseEtaFixedPhaseStableCoreSubmodule`; a duplicate local family breaks
subtraction and finite-sum APIs for the previously constructed linear maps. -/

""",
        "new": """/- Re-expose the same canonical subtype instances in this namespace. These are
definitionally identical to the instances used by the previously constructed
linear maps, unlike a separately built `Submodule.addCommGroup` family. -/
noncomputable local instance fixedPhaseDensityCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n))

noncomputable local instance fixedPhaseDensityCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact inferInstanceAs
    (Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n))

""",
    },
    {
        "name": "general covariance reverse bridge",
        "old": """  intro γ z
  have hCov := SmoothCompactWeightCore.covariance u γ z
  simpa [rawOfSmoothCompactWeightCore,
""",
        "new": """  intro γ z
  have hCov := SmoothCompactWeightCore.covariance u γ z
  rw [← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov
  simpa [rawOfSmoothCompactWeightCore,
""",
    },
    {
        "name": "fully qualify WeightSection additive evaluation",
        "old": "simp only [map_add, WeightSection.add_apply, mul_add]",
        "new": "simp only [map_add, HalfIntegralMultiplier.WeightSection.add_apply, mul_add]",
        "expected": 2,
    },
    {
        "name": "fully qualify WeightSection scalar evaluation",
        "old": "simp only [map_smul, WeightSection.smul_apply]",
        "new": "simp only [map_smul, HalfIntegralMultiplier.WeightSection.smul_apply]",
        "expected": 2,
    },
    {
        "name": "typed NNReal hyperbolic density division",
        "old": """noncomputable def hyperbolicDensity (z : ℍ) : NNReal :=
  ((⟨z.im, z.im_pos.le⟩ : NNReal)⁻¹) ^ 2
""",
        "new": """noncomputable def hyperbolicDensity (z : ℍ) : NNReal :=
  ((1 : NNReal) / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2
""",
    },
    {
        "name": "explicit horizontal gauge exponent",
        "old": """  have hProd :=
    dx_mul (realSmooth_complexHeightRpow _)
      u.1.1.2 z
""",
        "new": """  have hProd :=
    dx_mul (realSmooth_complexHeightRpow (euclideanGaugeExponent n))
      u.1.1.2 z
""",
    },
    {
        "name": "explicit vertical gauge exponent",
        "old": """  have hProd :=
    dy_mul (realSmooth_complexHeightRpow _)
      u.1.1.2 z
""",
        "new": """  have hProd :=
    dy_mul (realSmooth_complexHeightRpow (euclideanGaugeExponent n))
      u.1.1.2 z
""",
    },
]


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_digest = digest(text)
    print(f"input_sha256={input_digest}")
    if input_digest == EXPECTED_OUTPUT_SHA256:
        print("[pass341] already applied")
        return 0
    if input_digest != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass341 input sha256: {input_digest}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    for item in REPLACEMENTS:
        old = item["old"]
        new = item["new"]
        expected = item.get("expected", 1)
        count = text.count(old)
        print(f'{item["name"]}: expected={expected} actual={count}')
        if count != expected:
            raise RuntimeError(
                f'{item["name"]}: expected {expected} occurrence(s), found {count}'
            )
        text = text.replace(old, new)

    output_digest = digest(text)
    print(f"output_sha256={output_digest}")
    if output_digest != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass341 output sha256: {output_digest}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print(
        "[pass341] canonical subtype instances, covariance direction, "
        "qualified section API, density, and derivative frontiers repaired"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
