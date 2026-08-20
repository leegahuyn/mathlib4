from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "d38f2f58649a4acda650c92d4a36a6df063b86dbe144ce958dc1c1a096168189"
EXPECTED_OUTPUT_SHA256 = "706546d7c3329c1982fa223b3262ea5953180a92d1e40ea9c17c98c6da1ac6e0"


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
        print("[pass330] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass330 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    # PASS327 left a standalone doc comment immediately before the real
    # declaration docstring. Lean treats the first as an unattached command
    # docstring and the next one as a syntax error, cascading through the whole
    # graph-completion section.
    text = replace_exact(
        text,
        "/-- `InverseEtaFixedPhaseCore` uses the canonical `Submodule` subtype instances. -/\n",
        "",
        "FunctionalAnalysis remove orphan fixed-phase doc comment",
    )

    text = replace_exact(
        text,
        """  simpa only [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    ← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance
        compactInverseEtaOrbitZeroWeightCore γ z
""",
        """  simpa only [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance
        compactInverseEtaOrbitZeroWeightCore γ z
""",
        "FunctionalAnalysis orbit-zero covariance action direction",
    )
    text = replace_exact(
        text,
        """  simpa only [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    ← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance u γ z
""",
        """  simpa only [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance u γ z
""",
        "FunctionalAnalysis raw covariance action direction",
    )

    text = replace_exact(
        text,
        """    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  simp only [constantCompactCuspTail_truncation, sub_self, norm_zero]
""",
        """    ‖(constantCompactCuspTail C hC).truncation n - C‖ = 0 := by
  have hNorm := congrArg norm
    (constantCompactCuspTail_tail_eq_zero C hC n)
  simpa only [norm_zero] using hNorm
""",
        "FunctionalAnalysis exact-tail norm from proved zero equality",
    )

    text = replace_exact(
        text,
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
        """theorem upstairsCuspPartitionPiece_realSmooth (N : ℕ) :
    RealSmooth (upstairsCuspPartitionPiece N) := by
  cases N with
  | zero =>
      have hEq : upstairsCuspPartitionPiece 0 = upstairsCuspCutoff 0 := by
        funext z
        rfl
      rw [hEq]
      exact upstairsCuspCutoff_realSmooth 0
  | succ N =>
      have hEq : upstairsCuspPartitionPiece (N + 1) =
          upstairsCuspCutoff (N + 1) - upstairsCuspCutoff N := by
        funext z
        simp [upstairsCuspPartitionPiece, quotientCuspPartitionPiece,
          upstairsCuspCutoff, quotientCuspCutoffReal_mk]
      rw [hEq]
      exact (upstairsCuspCutoff_realSmooth (N + 1)).sub
        (upstairsCuspCutoff_realSmooth N)
""",
        "FunctionalAnalysis upstairs partition smoothness by function equality",
    )
    text = replace_exact(
        text,
        """theorem upstairsCuspPartitionPiece_gammaTwo_invariant (N : ℕ)
    (γ : GammaTwo) (z : ℍ) :
    upstairsCuspPartitionPiece N
        (((γ : GammaTwo) : SL(2, ℤ)) • z) =
      upstairsCuspPartitionPiece N z := by
  exact congrArg
    (fun q : GammaTwoQuotient ↦ (quotientCuspPartitionPiece N q : ℂ))
    (gammaTwoQuotientMk_gamma_smul γ z)
""",
        """theorem upstairsCuspPartitionPiece_gammaTwo_invariant (N : ℕ)
    (γ : GammaTwo) (z : ℍ) :
    upstairsCuspPartitionPiece N
        (((γ : GammaTwo) : SL(2, ℤ)) • z) =
      upstairsCuspPartitionPiece N z := by
  change (quotientCuspPartitionPiece N
      (gammaTwoQuotientMk (((γ : GammaTwo) : SL(2, ℤ)) • z)) : ℂ) =
    (quotientCuspPartitionPiece N (gammaTwoQuotientMk z) : ℂ)
  rw [show (((γ : GammaTwo) : SL(2, ℤ)) • z) = γ • z from rfl,
    gammaTwoQuotientMk_gamma_smul]
""",
        "FunctionalAnalysis upstairs partition GammaTwo invariance",
    )
    text = replace_exact(
        text,
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
        """theorem upstairsCuspPartitionPiece_quotientCompact (N : ℕ) :
    HasQuotientCompactSupport (upstairsCuspPartitionPiece N) := by
  cases N with
  | zero =>
      have hEq : upstairsCuspPartitionPiece 0 = upstairsCuspCutoff 0 := by
        funext z
        rfl
      rw [hEq]
      exact upstairsCuspCutoff_quotientCompact 0
  | succ N =>
      have hEq : upstairsCuspPartitionPiece (N + 1) =
          upstairsCuspCutoff (N + 1) - upstairsCuspCutoff N := by
        funext z
        simp [upstairsCuspPartitionPiece, quotientCuspPartitionPiece,
          upstairsCuspCutoff, quotientCuspCutoffReal_mk]
      rw [hEq]
      simpa only [sub_eq_add_neg] using
        (upstairsCuspCutoff_quotientCompact (N + 1)).add
          ((upstairsCuspCutoff_quotientCompact N).smul (-1))
""",
        "FunctionalAnalysis upstairs partition compact support by function equality",
    )

    text = replace_exact(
        text,
        """  rw [raiseRaw, dx_mul hχ hf, dy_mul hχ hf]
  simp only [Pi.mul_apply]
  ring
""",
        """  simp only [raiseRaw, dx_mul hχ hf, dy_mul hχ hf, Pi.mul_apply]
  ring
""",
        "FunctionalAnalysis exact raising product rule normalization",
    )
    text = replace_exact(
        text,
        """  rw [lowerRaw, dx_mul hχ hf, dy_mul hχ hf]
  simp only [Pi.mul_apply]
  ring
""",
        """  simp only [lowerRaw, dx_mul hχ hf, dy_mul hχ hf, Pi.mul_apply]
  ring
""",
        "FunctionalAnalysis exact lowering product rule normalization",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass330 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass330] FunctionalAnalysis syntax and first independent frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
