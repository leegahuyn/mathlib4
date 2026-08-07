from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "8c0b0797155d3ae4f8f05b2d38d36552a629c900b8e990aba1ff44b666b72e45"
EXPECTED_OUTPUT_SHA256 = "7a179ce46bcb210dbd8cbf30a19aeb7da65ffed24709a8844bf4a244a8e65de5"

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
        print("[pass334] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(f"unexpected pass334 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}")
    replacements = [
        (
            """  · intro hz
    refine ⟨z, ?_, rfl⟩
    simpa only [Function.mem_support, quotientPotentialShellReal,
      upstairsPotentialShell, potential_mk, Complex.ofReal_ne_zero] using hz
""",
            """  · intro hz
    refine ⟨z, ?_, rfl⟩
    change quotientPotentialShellReal N (gammaTwoQuotientMk z) ≠ 0 at hz
    have hzC :
        (quotientPotentialShellReal N (gammaTwoQuotientMk z) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hz
    simpa only [Function.mem_support, quotientPotentialShellReal,
      upstairsPotentialShell, potential_mk] using hzC
""",
            "potential shell support reverse",
        ),
        (
            """  rw [HasQuotientCompactSupport, quotientTSupport, tsupport,
    upstairsPotentialShell_projected_support]
""",
            """  rw [HasQuotientCompactSupport, quotientTSupport,
    upstairsPotentialShell_projected_support]
""",
            "potential shell compact support rewrite",
        ),
        (
            """  exact potentialShellCoreZero_at_point_ne_zero N (by simpa using hAt)
""",
            """  change
    upstairsPotentialShell N (potentialShellPoint N) *
      inverseEtaPaperOrbitZeroSeedSection (potentialShellPoint N) = 0 at hAt
  exact potentialShellCoreZero_at_point_ne_zero N hAt
""",
            "potential shell zero evaluation",
        ),
        (
            """  exact (realSmooth_complexHeightRpow (euclideanGaugeExponent n)).mul
    SmoothCompactWeightCore.realSmooth u.toSmoothCore
""",
            """  exact (realSmooth_complexHeightRpow (euclideanGaugeExponent n)).mul
    (SmoothCompactWeightCore.realSmooth u.toSmoothCore)
""",
            "euclidean gauge smoothness application",
        ),
        (
            """    (by simpa using
      UniformSpace.Completion.isUniformInducing_coe
        (OrbitPeterssonCore n)) u
""",
            """    (by
      simpa using
        (UniformSpace.Completion.isUniformInducing_coe
          (OrbitPeterssonCore n))) u
""",
            "completion inducing application",
        ),
        (
            """  simpa only [UniformSpace.Completion.norm_coe] using
    (orbitPeterssonCoreEuclideanIsometry n).norm_map u
""",
            """  simpa only [orbitPeterssonCoreEuclideanIsometry,
    UniformSpace.Completion.norm_coe] using
      (orbitPeterssonCoreEuclideanIsometry n).norm_map u
""",
            "completion embedding norm",
        ),
    ]
    for old, new, label in replacements:
        text = replace_once(text, old, new, label)
    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(f"unexpected pass334 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}")
    TARGET.write_text(text, encoding="utf-8")
    print("[pass334] FunctionalAnalysis potential-shell and Euclidean-completion frontier repaired")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
