from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "14350571cc83f03849f21d4f12ba09a97e3e8897a35bca8dd3e59103d9799468"
EXPECTED_OUTPUT_SHA256 = "3f79d5931a58750a0800351da6a0d44939d448fc61cab56a6cf0fb4195be0f37"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrence(s), found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass327] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass327 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    # PASS326 over-shortened the canonical fixed-phase core path.  The declaration
    # lives under HalfWeightDifferentialOperators, so repair every deterministic
    # full qualification introduced by PASS326.
    text = replace_exact(
        text,
        "Mock2FA.PaperCorrections.AutomorphicSobolev.InverseEtaFixedPhaseCore",
        "Mock2FA.PaperCorrections.AutomorphicSobolev.HalfWeightDifferentialOperators.InverseEtaFixedPhaseCore",
        "fixed-phase core canonical namespace",
        expected=445,
    )

    # These local instances are definitionally the canonical Submodule subtype
    # instances, so asking typeclass search to synthesize them while defining
    # themselves creates a recursive/stuck instance search.  Use the canonical
    # subtype instances directly.
    text = replace_exact(
        text,
        """/-- `InverseEtaFixedPhaseCore` is definitionally the subtype of the fixed-phase
submodule. Re-export the canonical subtype instances without passing through
`Submodule.toAddSubgroup`, whose reconstructed scalar-ring fields are not
judgmentally coherent with this opaque submodule. -/
noncomputable local instance fixedPhaseCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  infer_instance

noncomputable local instance fixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  infer_instance

""",
        "/-- `InverseEtaFixedPhaseCore` uses the canonical `Submodule` subtype instances. -/\n",
        "remove recursive fixed-phase subtype instances",
    )

    text = replace_exact(
        text,
        "tendsto_congr'",
        "Filter.tendsto_congr'",
        "current Filter tendsto congruence API",
        expected=2,
    )
    text = replace_exact(
        text,
        "      add_le_add_left hDerivSq' _\n",
        """      by
        simpa [add_comm] using
          add_le_add_left hDerivSq' (Real.exp r * S ^ 2 * F ^ 2)
""",
        "derivative-square additive bound orientation",
    )
    text = replace_exact(
        text,
        "    exact hZero t ht y hy\n",
        "    simpa using hZero t ht y hy\n",
        "eventual zero simplification",
    )

    # After the defining namespace closes, later appendices repeatedly reopen
    # different parent namespaces.  Fully qualify the stable PhysicalLocalL2 API
    # so those reopens cannot change name resolution.
    lines = text.splitlines(keepends=True)
    physical = (
        "Mock2FA.PaperCorrections.AutomorphicSobolev."
        "FixedPhaseClosedOperators.PhysicalLocalL2"
    )
    physical_count = 0
    for lineno, line in enumerate(lines, start=1):
        if lineno > 24970:
            line, count = re.subn(
                r"(?<![\w.])PhysicalLocalL2\.", physical + ".", line
            )
            physical_count += count
        lines[lineno - 1] = line
    print(f"PhysicalLocalL2 later references: expected=710 actual={physical_count}")
    if physical_count != 710:
        raise RuntimeError(
            f"unexpected PhysicalLocalL2 later-reference count: {physical_count}"
        )
    text = "".join(lines)

    # Definitions reported by Lean as depending on noncomputable canonical
    # structures.  Marking these noncomputable is the intended Lean API, not a
    # proof escape; their theorem statements and proofs are unchanged.
    noncomputable_replacements = [
        ("abbrev ambientChosenEuclideanMeasure : Measure ℂ :=",
         "noncomputable abbrev ambientChosenEuclideanMeasure : Measure ℂ :="),
        ("def successorGraphUnwrap (n : ℤ) :",
         "noncomputable def successorGraphUnwrap (n : ℤ) :"),
        ("def selectedCosetAction (q : GammaTwoRightCoset) (z : ℍ) : ℍ :=",
         "noncomputable def selectedCosetAction (q : GammaTwoRightCoset) (z : ℍ) : ℍ :="),
        ("def selectedCosetAmbientMap (q : GammaTwoRightCoset) (w : ℂ) : ℂ :=",
         "noncomputable def selectedCosetAmbientMap (q : GammaTwoRightCoset) (w : ℂ) : ℂ :="),
        ("def selectedCosetDenom (q : GammaTwoRightCoset) (z : ℍ) : ℂ :=",
         "noncomputable def selectedCosetDenom (q : GammaTwoRightCoset) (z : ℍ) : ℂ :="),
        ("def selectedCosetLowerLeft (q : GammaTwoRightCoset) : ℂ :=",
         "noncomputable def selectedCosetLowerLeft (q : GammaTwoRightCoset) : ℂ :="),
        ("def symm (p : ComplexPathPiece) : ComplexPathPiece where",
         "noncomputable def symm (p : ComplexPathPiece) : ComplexPathPiece where"),
        ("def reverse (C : ComplexBoundaryChain) : ComplexBoundaryChain :=",
         "noncomputable def reverse (C : ComplexBoundaryChain) : ComplexBoundaryChain :="),
        ("abbrev selectedHorocycleParameterMeasure : Measure ℝ :=",
         "noncomputable abbrev selectedHorocycleParameterMeasure : Measure ℝ :="),
        ("abbrev SelectedHorocycleL2 :=",
         "noncomputable abbrev SelectedHorocycleL2 :="),
        ("abbrev AmbientPlaneL2 :=",
         "noncomputable abbrev AmbientPlaneL2 :="),
        ("abbrev TwoTorusL2 :=",
         "noncomputable abbrev TwoTorusL2 :="),
        ("def discriminantCuspEpsilon (N : ℕ) : ℝ :=",
         "noncomputable def discriminantCuspEpsilon (N : ℕ) : ℝ :="),
        ("abbrev literalStageMeasure (Y : ℝ) : Measure ℍ :=",
         "noncomputable abbrev literalStageMeasure (Y : ℝ) : Measure ℍ :="),
        ("abbrev LiteralStageL2 (Y : ℝ) :=",
         "noncomputable abbrev LiteralStageL2 (Y : ℝ) :="),
        ("def reciprocalFourierTail (C : ℝ) (N : ℕ) : ℝ :=",
         "noncomputable def reciprocalFourierTail (C : ℝ) (N : ℕ) : ℝ :="),
        ("def gammaTwoLocalCuspQ (κ : GammaTwoCusp) (z : ℍ) : ℂ :=",
         "noncomputable def gammaTwoLocalCuspQ (κ : GammaTwoCusp) (z : ℍ) : ℂ :="),
        ("def ScalarScatteringJet.logDerivativeReal",
         "noncomputable def ScalarScatteringJet.logDerivativeReal"),
        ("def compactCokernelControl (K : X →L[ℂ] X) :",
         "noncomputable def compactCokernelControl (K : X →L[ℂ] X) :"),
        ("def adjointKernelToNormalizedAdjointKernel",
         "noncomputable def adjointKernelToNormalizedAdjointKernel"),
        ("abbrev HilbertCokernel (A : V →L[ℂ] W) := A.rangeᗮ",
         "noncomputable abbrev HilbertCokernel (A : V →L[ℂ] W) := A.rangeᗮ"),
        ("def rangeOrthogonalToCokernel",
         "noncomputable def rangeOrthogonalToCokernel"),
    ]
    for old, new in noncomputable_replacements:
        text = replace_exact(text, old, new, f"noncomputable: {old[:45]}")

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass327 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass327] namespace, current API, and computability frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
