from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "7a179ce46bcb210dbd8cbf30a19aeb7da65ffed24709a8844bf4a244a8e65de5"
EXPECTED_OUTPUT_SHA256 = "f79ef8961deeda98a6b21dd731061d0f6124729a7562240c7eacbc13dea44f4c"


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
        print("[pass335] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass335 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    replacements = [
        (
            """theorem potentialShellCoreZero_linearIndependent :
    LinearIndependent ℂ potentialShellCoreZero := by
  rw [linearIndependent_iff']
  intro s g hsum N hNs
""",
            """theorem potentialShellCoreZero_linearIndependent :
    LinearIndependent ℂ potentialShellCoreZero := by
  refine (linearIndependent_iff').2 ?_
  intro s g hsum N hNs
""",
            "FunctionalAnalysis linear-independent API",
        ),
        (
            """  have hlt :=
    potentialShellCoreZero_linearIndependent.lt_aleph0_of_finiteDimensional
  simpa [Cardinal.mk_nat] using hlt
""",
            """  have hlt :=
    potentialShellCoreZero_linearIndependent.lt_aleph0_of_finiteDimensional
  rw [Cardinal.mk_nat] at hlt
  exact (lt_irrefl _ hlt)
""",
            "FunctionalAnalysis finite-dimensional contradiction",
        ),
        (
            """theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  refine .pow (.div₀ continuous_const ?_ ?_) _
  · exact UpperHalfPlane.continuous_im.subtype_mk _
  · exact fun z => NNReal.ne_iff.mp z.im_ne_zero
""",
            """theorem hyperbolicDensity_continuous :
    Continuous hyperbolicDensity := by
  exact
    (continuous_const.div₀
      (UpperHalfPlane.continuous_im.subtype_mk _)
      (fun z => NNReal.ne_iff.mp z.im_ne_zero)).pow 2
""",
            "FunctionalAnalysis hyperbolic-density continuity",
        ),
    ]

    for old, new, label in replacements:
        text = replace_once(text, old, new, label)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass335 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass335] FunctionalAnalysis independence and continuity frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
