from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "57f084029aff8e8a4b95d13e0daa9890eaa036716da48b3a3352ac3023be1c25"
EXPECTED_OUTPUT_SHA256 = "0c052ff4a58c5945188c8b9b1e736b8ac2ef57bcb293fc05aacbdc60430ee6c3"

REPLACEMENTS = [{'name': 'remove incompatible graph-core local instances',
  'old': '/- `InverseEtaFixedPhaseCore` is an opaque abbreviation of a `Submodule`\n'
         'subtype. Keep one canonical additive/module instance family for every orbit\n'
         'index so graph-coordinate structures and completion constructions elaborate\n'
         'coherently throughout this namespace. -/\n'
         'noncomputable local instance fixedPhaseGraphCoreAddCommGroup (n : ℤ) :\n'
         '    AddCommGroup (InverseEtaFixedPhaseCore n) := by\n'
         '  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)\n'
         '  exact Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n)\n'
         '\n'
         'noncomputable local instance fixedPhaseGraphCoreModule (n : ℤ) :\n'
         '    Module ℂ (InverseEtaFixedPhaseCore n) := by\n'
         '  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)\n'
         '  exact Submodule.module (inverseEtaFixedPhaseStableCoreSubmodule n)\n'
         '\n',
  'new': '/- `InverseEtaFixedPhaseCore` is definitionally the subtype of the stable\n'
         'submodule.  Use the canonical subtype additive and module instances; introducing\n'
         'a second local instance family makes later linear maps definitionally\n'
         'incompatible with the already-constructed core maps. -/\n'
         '\n'},
 {'name': 'remove obsolete orbit-zero covariance rewrite',
  'old': '  rw [GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov\n'
         '  simpa [compactInverseEtaOrbitZeroSmoothQuotient,\n',
  'new': '  simpa [compactInverseEtaOrbitZeroSmoothQuotient,\n'},
 {'name': 'normalize compact-tail zero norm through simp',
  'old': '  calc\n'
         '    ‖(constantCompactCuspTail C hC).truncation n - C‖ = ‖(0 : ContinuousSesquilinearForm H)‖ :=\n'
         '      congrArg norm (constantCompactCuspTail_tail_eq_zero C hC n)\n'
         '    _ = 0 :=\n'
         '      (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = 0)\n',
  'new': '  simpa only [constantCompactCuspTail_tail_eq_zero, norm_zero]\n'},
 {'name': 'remove incompatible density-core local instances',
  'old': '/- `InverseEtaFixedPhaseCore` is an opaque abbreviation of a `Submodule`\n'
         'subtype. Keep one canonical additive/module instance family for every orbit\n'
         'index so subtraction of core-valued linear maps and finite-sum APIs elaborate\n'
         'coherently throughout the density section. -/\n'
         'noncomputable local instance fixedPhaseDensityCoreAddCommGroup (n : ℤ) :\n'
         '    AddCommGroup (InverseEtaFixedPhaseCore n) := by\n'
         '  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)\n'
         '  exact Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n)\n'
         '\n'
         'noncomputable local instance fixedPhaseDensityCoreModule (n : ℤ) :\n'
         '    Module ℂ (InverseEtaFixedPhaseCore n) := by\n'
         '  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)\n'
         '  exact Submodule.module (inverseEtaFixedPhaseStableCoreSubmodule n)\n'
         '\n',
  'new': '/- Keep the canonical subtype instances inherited from\n'
         '`inverseEtaFixedPhaseStableCoreSubmodule`; a duplicate local family breaks\n'
         'subtraction and finite-sum APIs for the previously constructed linear maps. -/\n'
         '\n'},
 {'name': 'remove obsolete general covariance rewrite',
  'old': '  rw [GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov\n  simpa [rawOfSmoothCompactWeightCore,\n',
  'new': '  simpa [rawOfSmoothCompactWeightCore,\n'},
 {'name': 'cutoff operator additive evaluation',
  'old': '    simp only [map_add, add_apply, mul_add]\n',
  'new': '    simp only [map_add, WeightSection.add_apply, mul_add]\n',
  'expected': 2},
 {'name': 'cutoff operator scalar evaluation',
  'old': '    simp only [map_smul, smul_eq_mul]\n    ring\n',
  'new': '    simp only [map_smul, WeightSection.smul_apply]\n    ring\n',
  'expected': 2},
 {'name': 'explicit NNReal inverse density',
  'old': 'noncomputable def hyperbolicDensity (z : ℍ) : NNReal :=\n  (1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2\n',
  'new': 'noncomputable def hyperbolicDensity (z : ℍ) : NNReal :=\n  ((⟨z.im, z.im_pos.le⟩ : NNReal)⁻¹) ^ 2\n'},
 {'name': 'apply horizontal product rule at the point',
  'old': '  have hProd := congrFun\n    (dx_mul (realSmooth_complexHeightRpow _)\n      u.1.1.2) z\n',
  'new': '  have hProd :=\n    dx_mul (realSmooth_complexHeightRpow _)\n      u.1.1.2 z\n'},
 {'name': 'apply vertical product rule at the point',
  'old': '  have hProd := congrFun\n    (dy_mul (realSmooth_complexHeightRpow _)\n      u.1.1.2) z\n',
  'new': '  have hProd :=\n    dy_mul (realSmooth_complexHeightRpow _)\n      u.1.1.2 z\n'}]


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_digest = digest(text)
    print(f"input_sha256={input_digest}")
    if input_digest == EXPECTED_OUTPUT_SHA256:
        print("[pass340] already applied")
        return 0
    if input_digest != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass340 input sha256: {input_digest}; "
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
            f"unexpected pass340 output sha256: {output_digest}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print(
        "[pass340] canonical subtype instances, covariance, operator linearity, "
        "NNReal density, and pointwise derivative frontiers repaired"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
