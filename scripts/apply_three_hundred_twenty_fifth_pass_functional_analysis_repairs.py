from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "cbe40f444a0fd843f89f87608b5f962cad774375d5daadf124b62ab155165350"
EXPECTED_OUTPUT_SHA256 = "6c557bc718c2a9259fd9df442b792bb94a031dc54b61876eb7c8900676daaaa8"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    old_count = text.count(old)
    print(f"{label}: expected=1 actual={old_count}")
    if old_count != 1:
        raise RuntimeError(
            f"{label}: expected exactly one unrepaired occurrence, found {old_count}"
        )
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass325] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass325 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    replacements = [
        (
            """noncomputable local instance fixedPhaseCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) :=
  Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n)

noncomputable local instance fixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) :=
  Submodule.module (inverseEtaFixedPhaseStableCoreSubmodule n)
""",
            """noncomputable local instance fixedPhaseCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  infer_instance

noncomputable local instance fixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  infer_instance
""",
            "FunctionalAnalysis canonical fixed-phase subtype instances",
        ),
        (
            """  simpa [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
""",
            """  simpa [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
""",
            "FunctionalAnalysis orbit-zero covariance action",
        ),
        (
            """    (peterssonCompletionEmbedding_denseRange M)
    (fun u => by
      rw [NNReal.coe_one, one_mul, peterssonCompletionEmbedding,
        PeterssonCoreSpace.norm_toCompletion])
""",
            """    (peterssonCompletionEmbedding_denseRange M)
    (fun u => by
      rw [NNReal.coe_one, one_mul]
      change ‖u‖ ≤ ‖PeterssonCoreSpace.toCompletion u‖
      exact (PeterssonCoreSpace.norm_toCompletion u).ge)
""",
            "FunctionalAnalysis completion embedding norm bound",
        ),
        (
            """  rw [rankOneForm_apply, rankOneForm_apply, star_mul']
  calc
    star (inner ℂ φ v) * star (inner ℂ u φ) =
        inner ℂ v φ * inner ℂ φ u :=
      congrArg₂ (· * ·) (inner_conj_symm v φ) (inner_conj_symm φ u)
    _ = inner ℂ φ u * inner ℂ v φ := mul_comm _ _
""",
            """  rw [rankOneForm_apply, rankOneForm_apply, star_mul']
  calc
    star (inner ℂ u φ) * star (inner ℂ φ v) =
        inner ℂ φ u * inner ℂ v φ :=
      congrArg₂ (· * ·) (inner_conj_symm φ u) (inner_conj_symm v φ)
    _ = inner ℂ v φ * inner ℂ φ u := mul_comm _ _
""",
            "FunctionalAnalysis rank-one conjugate symmetry order",
        ),
        (
            """  rw [constantCompactCuspTail_truncation]
  exact norm_eq_zero.mpr (sub_self C)
""",
            """  rw [constantCompactCuspTail_truncation, sub_self, norm_zero]
""",
            "FunctionalAnalysis constant compact-tail norm",
        ),
        (
            """  rw [pulledBackKernelForm_apply, pulledBackKernelForm_apply, star_mul']
  calc
    star (inner ℂ φ (B v)) * star (inner ℂ (B u) φ) =
        inner ℂ (B v) φ * inner ℂ φ (B u) :=
      congrArg₂ (· * ·)
        (inner_conj_symm (B v) φ) (inner_conj_symm φ (B u))
    _ = inner ℂ φ (B u) * inner ℂ (B v) φ := mul_comm _ _
""",
            """  rw [pulledBackKernelForm_apply, pulledBackKernelForm_apply, star_mul']
  calc
    star (inner ℂ (B u) φ) * star (inner ℂ φ (B v)) =
        inner ℂ φ (B u) * inner ℂ (B v) φ :=
      congrArg₂ (· * ·)
        (inner_conj_symm φ (B u)) (inner_conj_symm (B v) φ)
    _ = inner ℂ (B v) φ * inner ℂ φ (B u) := mul_comm _ _
""",
            "FunctionalAnalysis pulled-back conjugate symmetry order",
        ),
        (
            """    ‖(graphBaseKernelCuspTail n φ).truncation Y -
        graphBaseKernelForm n φ‖ = 0 := by
  simp
""",
            """    ‖(graphBaseKernelCuspTail n φ).truncation Y -
        graphBaseKernelForm n φ‖ = 0 := by
  simpa only [graphBaseKernelCuspTail] using
    constantCompactCuspTail_tail_norm_eq_zero
      (graphBaseKernelForm n φ) (graphBaseKernelForm_isCompact n φ) Y
""",
            "FunctionalAnalysis graph-kernel compact-tail norm",
        ),
        (
            """    ‖(compactCoreKernelCuspTail n φ₀).truncation Y -
        compactCoreKernelForm n φ₀‖ = 0 := by
  simp
""",
            """    ‖(compactCoreKernelCuspTail n φ₀).truncation Y -
        compactCoreKernelForm n φ₀‖ = 0 := by
  simpa only [compactCoreKernelCuspTail] using
    constantCompactCuspTail_tail_norm_eq_zero
      (compactCoreKernelForm n φ₀) (compactCoreKernelForm_isCompact n φ₀) Y
""",
            "FunctionalAnalysis compact-core compact-tail norm",
        ),
        (
            """  simpa [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
""",
            """  simpa [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
""",
            "FunctionalAnalysis raw compact-core covariance action",
        ),
    ]

    for old, new, label in replacements:
        text = replace_once(text, old, new, label)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass325 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )

    TARGET.write_text(text, encoding="utf-8")
    print("[pass325] FunctionalAnalysis subtype, covariance, and compact-tail frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
