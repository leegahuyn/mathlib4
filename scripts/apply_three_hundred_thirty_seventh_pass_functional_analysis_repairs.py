from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "204acd949c17f55013487819b215886ae5c1c5fb4d125d4683871f8fb94847ad"
EXPECTED_OUTPUT_SHA256 = "a1019626213bcd9792a1d6f8a19412b9d85d14ff94a2994b444d194e1c8d6128"


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
        print("[pass337] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass337 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_once(
        text,
        """open WeightCorePetersson WeightCorePetersson.PeterssonCoreSpace
open FixedPhasePeterssonCoordinates

/-- The three concrete shifted Petersson coordinates on the canonical
fixed-phase differential core. -/
""",
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
        "FunctionalAnalysis fixed-phase graph core canonical instances",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass337 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass337] fixed-phase graph completion instance frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
