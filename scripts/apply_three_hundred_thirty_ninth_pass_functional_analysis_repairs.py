from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "548dd3afbdab53c778d14dd65c86c53f71ace84a0ea01b5d3e93662cd6cc3d0a"
EXPECTED_OUTPUT_SHA256 = "11f5d0b53aa640d44169a05d02c0a0cbe90dfe8fa53cab4e4f66131a01a089fd"


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
        print("[pass339] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass339 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(
        text,
        """  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    simp [invariantCutoffTimesOrbitSection_apply,
      InverseEtaFixedPhaseCore.toWeightSection_apply, mul_add]
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    simp [invariantCutoffTimesOrbitSection_apply,
      InverseEtaFixedPhaseCore.toWeightSection_apply]
    ring
""",
        """  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change
      (cuspCutoffSmoothQuotient N : ℍ → ℂ) z *
          (InverseEtaFixedPhaseCore.toWeightSection n (u + v)) z =
        (cuspCutoffSmoothQuotient N : ℍ → ℂ) z *
            (InverseEtaFixedPhaseCore.toWeightSection n u) z +
          (cuspCutoffSmoothQuotient N : ℍ → ℂ) z *
            (InverseEtaFixedPhaseCore.toWeightSection n v) z
    simp only [map_add, add_apply, mul_add]
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change
      (cuspCutoffSmoothQuotient N : ℍ → ℂ) z *
          (InverseEtaFixedPhaseCore.toWeightSection n (c • u)) z =
        c *
          ((cuspCutoffSmoothQuotient N : ℍ → ℂ) z *
            (InverseEtaFixedPhaseCore.toWeightSection n u) z)
    simp only [map_smul, smul_eq_mul]
    ring
""",
        "cusp cutoff operator pointwise linearity",
    )

    text = replace_exact(
        text,
        """  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    simp [invariantCutoffTimesOrbitSection_apply,
      InverseEtaFixedPhaseCore.toWeightSection_apply, mul_add]
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    simp [invariantCutoffTimesOrbitSection_apply,
      InverseEtaFixedPhaseCore.toWeightSection_apply]
    ring
""",
        """  map_add' u v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change
      (cuspPartitionPieceSmoothQuotient N : ℍ → ℂ) z *
          (InverseEtaFixedPhaseCore.toWeightSection n (u + v)) z =
        (cuspPartitionPieceSmoothQuotient N : ℍ → ℂ) z *
            (InverseEtaFixedPhaseCore.toWeightSection n u) z +
          (cuspPartitionPieceSmoothQuotient N : ℍ → ℂ) z *
            (InverseEtaFixedPhaseCore.toWeightSection n v) z
    simp only [map_add, add_apply, mul_add]
  map_smul' c u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change
      (cuspPartitionPieceSmoothQuotient N : ℍ → ℂ) z *
          (InverseEtaFixedPhaseCore.toWeightSection n (c • u)) z =
        c *
          ((cuspPartitionPieceSmoothQuotient N : ℍ → ℂ) z *
            (InverseEtaFixedPhaseCore.toWeightSection n u) z)
    simp only [map_smul, smul_eq_mul]
    ring
""",
        "cusp partition operator pointwise linearity",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass339 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass339] cutoff-operator linearity frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
