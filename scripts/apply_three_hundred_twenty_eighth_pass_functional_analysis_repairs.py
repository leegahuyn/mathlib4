from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "3f79d5931a58750a0800351da6a0d44939d448fc61cab56a6cf0fb4195be0f37"
EXPECTED_OUTPUT_SHA256 = "f39bad641a544d23c59871b91d3e3eb677cf8fca25e0bf49c10d28d48503b576"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(
    text: str, old: str, new: str, label: str, expected: int = 1
) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(
            f"{label}: expected {expected} occurrence(s), found {count}"
        )
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass328] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass328 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    standalone_conj = re.compile(r"(?<!Complex\.)continuous_conj\.comp")
    conj_count = len(standalone_conj.findall(text))
    print(f"FunctionalAnalysis qualify continuous conjugation: expected=2 actual={conj_count}")
    if conj_count != 2:
        raise RuntimeError(
            f"expected two unqualified continuous_conj.comp occurrences, found {conj_count}"
        )
    text = standalone_conj.sub("Complex.continuous_conj.comp", text)

    replacements = [
        (
            """theorem constantCompactCuspTail_tail_norm_eq_zero
    (C : ContinuousSesquilinearForm H) (hC : IsCompactOperator C) (n : ℕ) :
    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  rw [constantCompactCuspTail_truncation, sub_self, norm_zero]
""",
            """theorem constantCompactCuspTail_tail_norm_eq_zero
    (C : ContinuousSesquilinearForm H) (hC : IsCompactOperator C) (n : ℕ) :
    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  simp only [constantCompactCuspTail_truncation, sub_self, norm_zero]
""",
            "FunctionalAnalysis constant compact-tail norm simplification",
        ),
        (
            """  simpa [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance
        compactInverseEtaOrbitZeroWeightCore γ z
""",
            """  simpa only [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    ← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance
        compactInverseEtaOrbitZeroWeightCore γ z
""",
            "FunctionalAnalysis orbit-zero covariance action orientation",
        ),
        (
            """  simpa [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance u γ z
""",
            """  simpa only [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    ← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance u γ z
""",
            "FunctionalAnalysis raw covariance action orientation",
        ),
        (
            """  · intro hz
    refine ⟨z, ?_, rfl⟩
    simpa only [Function.mem_support, quotientCuspCutoffReal_mk,
      upstairsCuspCutoff, Complex.ofReal_ne_zero] using hz
""",
            """  · intro hz
    refine ⟨z, ?_, rfl⟩
    change quotientCuspCutoffReal N (gammaTwoQuotientMk z) ≠ 0 at hz
    rw [quotientCuspCutoffReal_mk] at hz
    simpa only [Function.mem_support, upstairsCuspCutoff,
      Complex.ofReal_ne_zero] using hz
""",
            "FunctionalAnalysis projected cutoff support reverse direction",
        ),
        (
            """  rw [HasQuotientCompactSupport, quotientTSupport, tsupport,
    upstairsCuspCutoff_projected_support]
""",
            """  rw [HasQuotientCompactSupport, quotientTSupport,
    upstairsCuspCutoff_projected_support]
""",
            "FunctionalAnalysis remove unrelated tsupport rewrite",
        ),
        (
            """theorem quotientCuspPartitionPiece_hasCompactSupport (N : ℕ) :
    HasCompactSupport (quotientCuspPartitionPiece N) := by
  cases N with
  | zero => exact quotientCuspCutoffReal_hasCompactSupport 0
  | succ N =>
      simpa only [quotientCuspPartitionPiece, sub_eq_add_neg] using
        (quotientCuspCutoffReal_hasCompactSupport (N + 1)).add
          (quotientCuspCutoffReal_hasCompactSupport N).neg
""",
            """theorem quotientCuspPartitionPiece_hasCompactSupport (N : ℕ) :
    HasCompactSupport (quotientCuspPartitionPiece N) := by
  cases N with
  | zero => exact quotientCuspCutoffReal_hasCompactSupport 0
  | succ N =>
      change HasCompactSupport
        (quotientCuspCutoffReal (N + 1) - quotientCuspCutoffReal N)
      simpa only [sub_eq_add_neg] using
        (quotientCuspCutoffReal_hasCompactSupport (N + 1)).add
          (quotientCuspCutoffReal_hasCompactSupport N).neg
""",
            "FunctionalAnalysis quotient partition compact support",
        ),
        (
            """theorem upstairsCuspPartitionPiece_realSmooth (N : ℕ) :
    RealSmooth (upstairsCuspPartitionPiece N) := by
  cases N with
  | zero =>
      simpa only [upstairsCuspPartitionPiece,
        quotientCuspPartitionPiece, quotientCuspCutoffReal_mk,
        upstairsCuspCutoff] using
        upstairsCuspCutoff_realSmooth 0
  | succ N =>
      simpa only [upstairsCuspPartitionPiece,
        quotientCuspPartitionPiece, quotientCuspCutoffReal_mk,
        upstairsCuspCutoff, Complex.ofReal_sub] using
          (upstairsCuspCutoff_realSmooth (N + 1)).sub
            (upstairsCuspCutoff_realSmooth N)
""",
            """theorem upstairsCuspPartitionPiece_realSmooth (N : ℕ) :
    RealSmooth (upstairsCuspPartitionPiece N) := by
  cases N with
  | zero =>
      change RealSmooth (upstairsCuspCutoff 0)
      exact upstairsCuspCutoff_realSmooth 0
  | succ N =>
      change RealSmooth
        (upstairsCuspCutoff (N + 1) - upstairsCuspCutoff N)
      exact (upstairsCuspCutoff_realSmooth (N + 1)).sub
        (upstairsCuspCutoff_realSmooth N)
""",
            "FunctionalAnalysis upstairs partition smoothness",
        ),
        (
            """theorem upstairsCuspPartitionPiece_gammaTwo_invariant (N : ℕ)
    (γ : GammaTwo) (z : ℍ) :
    upstairsCuspPartitionPiece N
        (((γ : GammaTwo) : SL(2, ℤ)) • z) =
      upstairsCuspPartitionPiece N z := by
  simp only [upstairsCuspPartitionPiece,
    gammaTwoQuotientMk_gamma_smul]
""",
            """theorem upstairsCuspPartitionPiece_gammaTwo_invariant (N : ℕ)
    (γ : GammaTwo) (z : ℍ) :
    upstairsCuspPartitionPiece N
        (((γ : GammaTwo) : SL(2, ℤ)) • z) =
      upstairsCuspPartitionPiece N z := by
  exact congrArg
    (fun q : GammaTwoQuotient ↦ (quotientCuspPartitionPiece N q : ℂ))
    (gammaTwoQuotientMk_gamma_smul γ z)
""",
            "FunctionalAnalysis upstairs partition invariance",
        ),
        (
            """theorem upstairsCuspPartitionPiece_quotientCompact (N : ℕ) :
    HasQuotientCompactSupport (upstairsCuspPartitionPiece N) := by
  cases N with
  | zero =>
      simpa only [upstairsCuspPartitionPiece,
        quotientCuspPartitionPiece, quotientCuspCutoffReal_mk,
        upstairsCuspCutoff] using upstairsCuspCutoff_quotientCompact 0
  | succ N =>
      simpa only [upstairsCuspPartitionPiece,
        quotientCuspPartitionPiece, quotientCuspCutoffReal_mk,
        upstairsCuspCutoff, Complex.ofReal_sub, sub_eq_add_neg] using
        (upstairsCuspCutoff_quotientCompact (N + 1)).add
          (upstairsCuspCutoff_quotientCompact N).smul (-1)
""",
            """theorem upstairsCuspPartitionPiece_quotientCompact (N : ℕ) :
    HasQuotientCompactSupport (upstairsCuspPartitionPiece N) := by
  cases N with
  | zero =>
      change HasQuotientCompactSupport (upstairsCuspCutoff 0)
      exact upstairsCuspCutoff_quotientCompact 0
  | succ N =>
      change HasQuotientCompactSupport
        (upstairsCuspCutoff (N + 1) - upstairsCuspCutoff N)
      simpa only [sub_eq_add_neg] using
        (upstairsCuspCutoff_quotientCompact (N + 1)).add
          ((upstairsCuspCutoff_quotientCompact N).smul (-1))
""",
            "FunctionalAnalysis upstairs partition compact support",
        ),
    ]

    for old, new, label in replacements:
        text = replace_exact(text, old, new, label)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass328 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass328] action, cusp partition, support, and conjugation frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
