from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "48707b6952a1aad8e19fd47b5f3d4f74d4e0b0e66262ead87386512786083c3e"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_required(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrence(s), found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass341 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_required(
        text,
        "  exact Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n)",
        "  exact Module.addCommMonoidToAddCommGroup ℂ",
        "FunctionalAnalysis derive stable-core additive groups from complex modules",
        expected=2,
    )
    text = replace_required(
        text,
        "  rw [GammaTwoQuotientGeometry.gammaTwoToSL2Real_smul] at hCov\n",
        "",
        "FunctionalAnalysis remove obsolete GammaTwo covariance rewrites",
        expected=2,
    )
    text = replace_required(
        text,
        """    _ = 0 :=
      (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = 0)""",
        """    _ = 0 := by
      simp""",
        "FunctionalAnalysis infer the typed zero sesquilinear-form norm",
    )
    text = replace_required(
        text,
        """  change
    InverseEtaFixedPhaseCore.raise n (cuspCutoffOperator M n u) -
      cuspCutoffOperator M (n + 1)
        (InverseEtaFixedPhaseCore.raise n u) = 0
  rw [hMu, hMr, sub_self]""",
        """  simpa only [raiseCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply, hMu, hMr, sub_self]""",
        "FunctionalAnalysis unfold the eventual raising commutator",
    )
    text = replace_required(
        text,
        """  change
    InverseEtaFixedPhaseCore.lower n (cuspCutoffOperator M n u) -
      cuspCutoffOperator M (n - 1)
        (InverseEtaFixedPhaseCore.lower n u) = 0
  rw [hMu, hMl, sub_self]""",
        """  simpa only [lowerCuspCutoffCommutator, LinearMap.sub_apply,
    LinearMap.comp_apply, hMu, hMl, sub_self]""",
        "FunctionalAnalysis unfold the eventual lowering commutator",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    TARGET.write_text(text, encoding="utf-8")
    print("[pass341] FunctionalAnalysis module, covariance, zero-norm, and commutator roots repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
