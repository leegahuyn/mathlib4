from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "6c557bc718c2a9259fd9df442b792bb94a031dc54b61876eb7c8900676daaaa8"
EXPECTED_OUTPUT_SHA256 = "14350571cc83f03849f21d4f12ba09a97e3e8897a35bca8dd3e59103d9799468"


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
        print("[pass326] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass326 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    # PASS327's 1000-error run exposed a large notation/namespace cascade.
    text = replace_exact(text, "𝒩", "𝓝", "neighborhood notation", expected=84)
    text = replace_exact(
        text,
        "open DefinitionOneSobolev.SmoothCompactCoreGeometry",
        "open SmoothCompactCoreGeometry",
        "SmoothCompactCoreGeometry namespace",
        expected=13,
    )
    text = replace_exact(
        text,
        "open DefinitionOneSobolev.HalfWeightDifferentialOperators",
        "open HalfWeightDifferentialOperators",
        "HalfWeightDifferentialOperators namespace",
        expected=3,
    )
    text = replace_exact(
        text,
        "open ExplicitDiscriminantPotential.CorePotentialForm\n",
        "",
        "obsolete CorePotentialForm namespace",
        expected=4,
    )
    text = replace_exact(
        text,
        "open ExplicitDiscriminantPotential.CorePotentialForm.FixedPhaseGraphPotential",
        "open ExplicitDiscriminantPotential.FixedPhaseGraphPotential",
        "FixedPhaseGraphPotential namespace",
        expected=4,
    )

    # The canonical fixed-phase core is a parent declaration of DefinitionOneSobolev,
    # not a child of FixedPhasePeterssonCoordinates.  Fully qualify P3+ uses so
    # later reopened namespaces cannot shadow or lose the declaration.
    lines = text.splitlines(keepends=True)
    rewritten: list[str] = []
    wrong_long = 0
    unqualified = 0
    old_long = (
        "DefinitionOneSobolev.FixedPhasePeterssonCoordinates."
        "InverseEtaFixedPhaseCore"
    )
    canonical = "Mock2FA.PaperCorrections.AutomorphicSobolev.InverseEtaFixedPhaseCore"
    for lineno, line in enumerate(lines, start=1):
        if lineno >= 36000:
            wrong_long += line.count(old_long)
            line = line.replace(old_long, canonical)
            line, count = re.subn(
                r"(?<![\w.])InverseEtaFixedPhaseCore\b",
                canonical,
                line,
            )
            unqualified += count
        rewritten.append(line)
    print(f"fixed-phase core old-qualified: expected=14 actual={wrong_long}")
    print(f"fixed-phase core unqualified P3+: expected=431 actual={unqualified}")
    if wrong_long != 14 or unqualified != 431:
        raise RuntimeError(
            f"unexpected fixed-phase core reference counts: {wrong_long}, {unqualified}"
        )
    text = "".join(rewritten)

    text = replace_exact(
        text,
        """  refine ⟨gammaTwoQuotientMk ⁻¹' U,
    (gammaTwoQuotientMk_isOpenQuotientMap.continuous.continuousAt)
      .preimage_mem_nhds hU, ?_⟩
""",
        """  refine ⟨gammaTwoQuotientMk ⁻¹' U,
    gammaTwoQuotientMk_isOpenQuotientMap.continuous.continuousAt hU, ?_⟩
""",
        "quotient-map neighborhood preimage",
    )
    text = replace_exact(
        text,
        """  rw [raiseRaw, dx_mul hχ hf, dy_mul hχ hf]
  ring
""",
        """  rw [raiseRaw, dx_mul hχ hf, dy_mul hχ hf]
  simp only [Pi.mul_apply]
  ring
""",
        "raising product-rule normalization",
    )
    text = replace_exact(
        text,
        """  rw [lowerRaw, dx_mul hχ hf, dy_mul hχ hf]
  ring
""",
        """  rw [lowerRaw, dx_mul hχ hf, dy_mul hχ hf]
  simp only [Pi.mul_apply]
  ring
""",
        "lowering product-rule normalization",
    )
    text = replace_exact(
        text,
        "  exact ⟨u, by rw [hN N le_rfl]⟩\n",
        "  exact ⟨u, congrArg (coreMap n) (hN N le_rfl)⟩\n",
        "cutoff range witness",
    )
    text = replace_exact(
        text,
        "abbrev CompatibleForcing\n"
        "    (n : ℤ) (t : ℝ) := (weakSchrodingerOperator n t).range",
        "noncomputable abbrev CompatibleForcing\n"
        "    (n : ℤ) (t : ℝ) := (weakSchrodingerOperator n t).range",
        "compatible forcing computability",
    )
    text = replace_exact(
        text,
        "abbrev WeightedWeakSobolev (n : ℤ) := weightedWeakSubmodule n",
        "noncomputable abbrev WeightedWeakSobolev (n : ℤ) := weightedWeakSubmodule n",
        "weighted weak Sobolev computability",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass326 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass326] broad namespace, notation, and proof frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
