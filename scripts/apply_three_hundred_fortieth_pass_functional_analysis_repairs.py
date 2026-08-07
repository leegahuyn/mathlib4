from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "11f5d0b53aa640d44169a05d02c0a0cbe90dfe8fa53cab4e4f66131a01a089fd"
EXPECTED_OUTPUT_SHA256 = "4b5e548d48fbd76e4de329fdc20afa3f915dbea800d5e4044ec097474dbe6731"


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
        print("[pass340] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass340 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(
        text,
        """theorem potentialShellCoreZero_support_subset (N : ℕ) :
    Function.support
        (fun z ↦ ((potentialShellCoreZero N :
          InverseEtaFixedPhaseCore 0) : SmoothQuotientCompactFunction) z) ⊆
      Function.support (upstairsPotentialShell N) := by
  intro z hz
  change upstairsPotentialShell N z *
    inverseEtaPaperOrbitZeroSeedSection z ≠ 0 at hz
  exact left_ne_zero_of_mul hz
""",
        """theorem potentialShellCoreZero_support_subset (N : ℕ) :
    Function.support
        (fun z ↦ ((potentialShellCoreZero N :
          InverseEtaFixedPhaseCore 0) : SmoothQuotientCompactFunction) z) ⊆
      Function.support (upstairsPotentialShell N) := by
  intro z hz
  have hz' :
      upstairsPotentialShell N z *
          inverseEtaPaperOrbitZeroSeedSection z ≠ 0 := by
    simpa only [Function.mem_support, potentialShellCoreZero_apply] using hz
  exact left_ne_zero_of_mul hz'
""",
        "potential shell support without coercion timeout",
    )

    text = replace_exact(
        text,
        """noncomputable def hyperbolicDensity (z : ℍ) : ℝ≥0 :=
  (1 / NNReal.mk z.im z.im_pos.le) ^ 2

theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  exact
    (continuous_const.div₀
      (UpperHalfPlane.continuous_im.subtype_mk _)
      (fun z => NNReal.ne_iff.mp z.im_ne_zero)).pow 2
""",
        """noncomputable def hyperbolicDensity (z : ℍ) : ℝ≥0 :=
  (1 / (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) ^ 2

theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  simpa only [hyperbolicDensity] using
    ((continuous_const.div₀
      (UpperHalfPlane.continuous_im.subtype_mk _)
      (fun z => NNReal.ne_iff.mp z.im_ne_zero)).pow 2)
""",
        "typed NNReal hyperbolic density",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass340 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass340] potential-shell support and NNReal density frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
