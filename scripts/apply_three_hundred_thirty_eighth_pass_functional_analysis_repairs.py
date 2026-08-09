from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "6e772d414fc0fb9b3ec532039a22a00f0d28e2884136bb0d841494d7bde3f2b1"
EXPECTED_OUTPUT_SHA256 = "1d150bcb8bd909e1bde7ce3577cf754386efcd7be2902d68a7c78b72b28d6b39"


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
        print("[pass338] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass338 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_once(
        text,
        """namespace PaperCorrections.AutomorphicSobolev.FixedPhaseDensity

open GammaTwoQuotientGeometry SmoothCompactCoreGeometry
open HalfWeightDifferentialOperators
open DefinitionOneSobolev
open DefinitionOneSobolev.WeightCorePetersson
open DefinitionOneSobolev.WeightCorePetersson.PeterssonCoreSpace
open DefinitionOneSobolev.FixedPhasePeterssonCoordinates
open DefinitionOneSobolev.FixedPhaseGraphCompletion

""",
        """namespace PaperCorrections.AutomorphicSobolev.FixedPhaseDensity

open GammaTwoQuotientGeometry SmoothCompactCoreGeometry
open HalfWeightDifferentialOperators
open DefinitionOneSobolev
open DefinitionOneSobolev.WeightCorePetersson
open DefinitionOneSobolev.WeightCorePetersson.PeterssonCoreSpace
open DefinitionOneSobolev.FixedPhasePeterssonCoordinates
open DefinitionOneSobolev.FixedPhaseGraphCompletion

/- `InverseEtaFixedPhaseCore` is an opaque abbreviation of a `Submodule`
subtype. Keep one canonical additive/module instance family for every orbit
index so subtraction of core-valued linear maps and finite-sum APIs elaborate
coherently throughout the density section. -/
noncomputable local instance fixedPhaseDensityCoreAddCommGroup (n : ℤ) :
    AddCommGroup (InverseEtaFixedPhaseCore n) := by
  change AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n)

noncomputable local instance fixedPhaseDensityCoreModule (n : ℤ) :
    Module ℂ (InverseEtaFixedPhaseCore n) := by
  change Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n)
  exact Submodule.module (inverseEtaFixedPhaseStableCoreSubmodule n)

""",
        "FunctionalAnalysis fixed-phase density algebra instances",
    )
    text = replace_once(
        text,
        """/-- `InverseEtaFixedPhaseCore 0` is definitionally a complex submodule subtype.
Expose its canonical additive group only for APIs that require a ring module. -/
noncomputable local instance fixedPhaseCoreZeroAddCommGroup :
    AddCommGroup (InverseEtaFixedPhaseCore 0) :=
  Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule 0)

""",
        "",
        "FunctionalAnalysis remove redundant zero-only additive instance",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass338 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass338] FunctionalAnalysis coherent fixed-phase core instances repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
