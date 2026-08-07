from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "a1019626213bcd9792a1d6f8a19412b9d85d14ff94a2994b444d194e1c8d6128"
EXPECTED_OUTPUT_SHA256 = "548dd3afbdab53c778d14dd65c86c53f71ace84a0ea01b5d3e93662cd6cc3d0a"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str) -> str:
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
        print("[pass338] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass338 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(
        text,
        """open WeightCorePetersson WeightCorePetersson.PeterssonCoreSpace
open FixedPhasePeterssonCoordinates

/-- `InverseEtaFixedPhaseCore` is definitionally the subtype of the canonical
fixed-phase submodule.  Pin the inherited additive and complex-module
structures explicitly so graph-coordinate constructions use one coherent
instance family instead of recursing through the opaque abbreviation. -/
noncomputable local instance fixedPhaseGraphCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n)

noncomputable local instance fixedPhaseGraphCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact Submodule.module (inverseEtaFixedPhaseStableCoreSubmodule n)

/-- The three concrete shifted Petersson coordinates on the canonical
fixed-phase differential core. -/
""",
        """open WeightCorePetersson WeightCorePetersson.PeterssonCoreSpace
open FixedPhasePeterssonCoordinates

/-- The three concrete shifted Petersson coordinates on the canonical
fixed-phase differential core. -/
""",
        "remove superseded local graph instances",
    )

    text = replace_exact(
        text,
        """/-- Canonical fixed-phase core at orbit index `n`. -/
noncomputable abbrev InverseEtaFixedPhaseCore (n : ℤ) : Type :=
  ↥(inverseEtaFixedPhaseStableCoreSubmodule n)

/-- Once the one-step covariance theorem has been proved, membership in the
""",
        """/-- Canonical fixed-phase core at orbit index `n`. -/
noncomputable abbrev InverseEtaFixedPhaseCore (n : ℤ) : Type :=
  ↥(inverseEtaFixedPhaseStableCoreSubmodule n)

/-- The fixed-phase core carries exactly the canonical additive-group
structure of its defining submodule.  This explicit instance avoids recursive
search through the reducible indexed abbreviation while remaining
definitionally coherent with the subtype operations. -/
noncomputable instance inverseEtaFixedPhaseCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) :=
  Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n)

/-- The fixed-phase core carries exactly the canonical complex-module
structure of its defining submodule. -/
noncomputable instance inverseEtaFixedPhaseCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) :=
  Submodule.module (inverseEtaFixedPhaseStableCoreSubmodule n)

/-- Once the one-step covariance theorem has been proved, membership in the
""",
        "global canonical fixed-phase core instances",
    )

    text = replace_exact(
        text,
        """  intro γ z
  simpa [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real,
    ← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance
        compactInverseEtaOrbitZeroWeightCore γ z
""",
        """  intro γ z
  have hCov :=
    SmoothCompactWeightCore.covariance
      compactInverseEtaOrbitZeroWeightCore γ z
  rw [GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov
  simpa [compactInverseEtaOrbitZeroSmoothQuotient,
    inverseEtaPaperOrbitFactor,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real] using hCov
""",
        "explicit orbit-zero covariance transport",
    )

    text = replace_exact(
        text,
        """  intro γ z
  simpa [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real,
    ← GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] using
      SmoothCompactWeightCore.covariance u γ z
""",
        """  intro γ z
  have hCov := SmoothCompactWeightCore.covariance u γ z
  rw [GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov
  simpa [rawOfSmoothCompactWeightCore,
    IsInverseEtaPaperOrbitCovariant, OrbitMultiplier,
    GammaTwoQuotientGeometry.gammaTwoToSL2Real] using hCov
""",
        "explicit general covariance transport",
    )

    text = replace_exact(
        text,
        """  calc
    ‖(constantCompactCuspTail C hC).truncation n - C‖ = ‖(0 : ContinuousSesquilinearForm H)‖ :=
      congrArg norm (constantCompactCuspTail_tail_eq_zero C hC n)
    _ = 0 := norm_zero
""",
        """  calc
    ‖(constantCompactCuspTail C hC).truncation n - C‖ = ‖(0 : ContinuousSesquilinearForm H)‖ :=
      congrArg norm (constantCompactCuspTail_tail_eq_zero C hC n)
    _ = 0 :=
      (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = 0)
""",
        "typed zero norm for the sesquilinear form",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass338 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass338] canonical fixed-phase core and covariance frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
