from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "ac23d9918a1daf9b534345ec4ef7eb382d081514c52bfb0dceda92d6e3633ade"
EXPECTED_OUTPUT_SHA256 = "bdcafba53aabd845cb860e0e3bd59b43a547da9f7d50810dcd3b4ad91819201b"


def sha256_text(text: str) -> str:
    import hashlib

    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    old_count = text.count(old)
    new_count = text.count(new)
    print(f"{label}: old={old_count} new={new_count}")
    if old_count == 1 and new_count == 0:
        return text.replace(old, new)
    if old_count == 0 and new_count == 1:
        return text
    raise RuntimeError(
        f"{label}: expected exactly one unrepaired or repaired occurrence, "
        f"found old={old_count}, new={new_count}"
    )


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = sha256_text(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass317] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass317 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_once(
        text,
        "open HalfIntegralMultiplier HalfWeightDifferentialOperators\n"
        "  GammaTwoQuotientGeometry\n"
        "open GammaTwoQuotientGreenBoundary\n",
        "open HalfIntegralMultiplier HalfWeightDifferentialOperators\n"
        "  GammaTwoQuotientGeometry\n"
        "open SmoothCompactCoreGeometry\n"
        "open GammaTwoQuotientGreenBoundary\n",
        "FunctionalAnalysis fixed-phase geometry namespace",
    )

    text = replace_once(
        text,
        "  refine ⟨zero_lt_one, fun u ↦ ?_⟩\n"
        "  change ‖u‖ ^ 2 ≤ (⟪u, u⟫_ℂ).re\n"
        "  exact (norm_sq_eq_re_inner (𝕜 := ℂ) u).le\n",
        "  refine ⟨zero_lt_one, fun u ↦ ?_⟩\n"
        "  rw [one_mul, Q.completionEnergyOperator_apply]\n"
        "  exact le_of_eq (norm_sq_eq_re_inner (𝕜 := ℂ) u)\n",
        "FunctionalAnalysis completion coercivity normalization",
    )

    text = replace_once(
        text,
        "abbrev ClosedBaseDomain :=\n"
        "  LinearMap.range Q.baseExtension.toLinearMap\n",
        "noncomputable abbrev ClosedBaseDomain :=\n"
        "  LinearMap.range Q.baseExtension.toLinearMap\n",
        "FunctionalAnalysis noncomputable closed base domain",
    )

    text = replace_once(
        text,
        "namespace FixedPhaseGraphCompletion\n\n"
        "open HalfIntegralMultiplier HalfWeightDifferentialOperators\n"
        "  GammaTwoQuotientGeometry\n"
        "open WeightCorePetersson WeightCorePetersson.PeterssonCoreSpace\n"
        "open FixedPhasePeterssonCoordinates\n\n"
        "/-- The three concrete shifted Petersson coordinates on the canonical\n",
        "namespace FixedPhaseGraphCompletion\n\n"
        "open HalfIntegralMultiplier HalfWeightDifferentialOperators\n"
        "  GammaTwoQuotientGeometry\n"
        "open WeightCorePetersson WeightCorePetersson.PeterssonCoreSpace\n"
        "open FixedPhasePeterssonCoordinates\n\n"
        "/-- Re-export the canonical subtype algebra structures at the opaque\n"
        "`InverseEtaFixedPhaseCore` boundary. -/\n"
        "noncomputable local instance fixedPhaseCoreAddCommGroup (n : ℤ) :\n"
        "    AddCommGroup (InverseEtaFixedPhaseCore n) :=\n"
        "  Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n)\n\n"
        "noncomputable local instance fixedPhaseCoreModule (n : ℤ) :\n"
        "    Module ℂ (InverseEtaFixedPhaseCore n) :=\n"
        "  Submodule.module (inverseEtaFixedPhaseStableCoreSubmodule n)\n\n"
        "/-- The three concrete shifted Petersson coordinates on the canonical\n",
        "FunctionalAnalysis fixed-phase subtype algebra structures",
    )

    replacements = [
        (
            "  have hEta := inverseEtaSection.covariance γ z\n",
            "  have hEta := WeightSection.covariance inverseEtaSection γ z\n",
            "FunctionalAnalysis orbit-zero seed covariance",
        ),
        (
            "  rw [upstairsCoreCutoff_gammaTwo_invariant,\n"
            "    inverseEtaSection.covariance]\n",
            "  rw [upstairsCoreCutoff_gammaTwo_invariant,\n"
            "    WeightSection.covariance inverseEtaSection]\n",
            "FunctionalAnalysis compact section covariance",
        ),
        (
            "    inverseEtaSection.covariance γ z\n",
            "    WeightSection.covariance inverseEtaSection γ z\n",
            "FunctionalAnalysis orbit-zero covariance",
        ),
        (
            "    compactInverseEtaPaperCore.toSection z =\n",
            "    SmoothCompactCore.toSection compactInverseEtaPaperCore z =\n",
            "FunctionalAnalysis compact paper core projection",
        ),
        (
            "    (fun u : SmoothCompactCore inverseEtaPaperCertificate ↦\n"
            "      u.toSection UpperHalfPlane.I) hZero\n",
            "    (fun u : SmoothCompactCore inverseEtaPaperCertificate ↦\n"
            "      SmoothCompactCore.toSection u UpperHalfPlane.I) hZero\n",
            "FunctionalAnalysis compact paper core evaluation",
        ),
        (
            "    (fun u : SmoothCompactWeightCore\n"
            "        inverseEtaPaperCertificate.multiplier ↦\n"
            "      u.toSection UpperHalfPlane.I) hZero\n",
            "    (fun u : SmoothCompactWeightCore\n"
            "        inverseEtaPaperCertificate.multiplier ↦\n"
            "      SmoothCompactWeightCore.toSection u UpperHalfPlane.I) hZero\n",
            "FunctionalAnalysis compact weight core evaluation",
        ),
        (
            "    (fun u : SmoothCompactWeightCore\n"
            "        (inverseEtaPaperOrbitMultiplier GammaTwo 0) ↦\n"
            "      u.toSection UpperHalfPlane.I) hZero\n",
            "    (fun u : SmoothCompactWeightCore\n"
            "        (inverseEtaPaperOrbitMultiplier GammaTwo 0) ↦\n"
            "      SmoothCompactWeightCore.toSection u UpperHalfPlane.I) hZero\n",
            "FunctionalAnalysis compact orbit-weight core evaluation",
        ),
        (
            "  ⟨⟨(compactInverseEtaOrbitZeroWeightCore.toSection : ℍ → ℂ),\n"
            "      compactInverseEtaOrbitZeroWeightCore.realSmooth⟩,\n"
            "    compactInverseEtaOrbitZeroWeightCore.quotientCompact⟩\n",
            "  ⟨⟨(SmoothCompactWeightCore.toSection\n"
            "        compactInverseEtaOrbitZeroWeightCore : ℍ → ℂ),\n"
            "      SmoothCompactWeightCore.realSmooth\n"
            "        compactInverseEtaOrbitZeroWeightCore⟩,\n"
            "    SmoothCompactWeightCore.quotientCompact\n"
            "      compactInverseEtaOrbitZeroWeightCore⟩\n",
            "FunctionalAnalysis compact orbit quotient projections",
        ),
        (
            "  change compactInverseEtaOrbitZeroWeightCore.toSection\n"
            "      (((γ : GammaTwo) : SL(2, ℤ)) • z) =\n"
            "    (inverseEtaPaperOrbitMultiplier GammaTwo 0).factor γ z *\n"
            "      compactInverseEtaOrbitZeroWeightCore.toSection z\n"
            "  rw [show (((γ : GammaTwo) : SL(2, ℤ)) • z) = γ • z from rfl]\n"
            "  exact compactInverseEtaOrbitZeroWeightCore.covariance γ z\n",
            "  simpa [compactInverseEtaOrbitZeroSmoothQuotient,\n"
            "    inverseEtaPaperOrbitFactor] using\n"
            "      SmoothCompactWeightCore.covariance\n"
            "        compactInverseEtaOrbitZeroWeightCore γ z\n",
            "FunctionalAnalysis compact orbit covariance projection",
        ),
    ]
    for old, new, label in replacements:
        text = replace_once(text, old, new, label)

    standalone_conj = re.compile(
        r"(?<![A-Za-z0-9_])Complex\.conj(?![A-Za-z0-9_])"
    )
    conj_count = len(standalone_conj.findall(text))
    print(f"FunctionalAnalysis standalone Complex.conj: {conj_count}")
    if conj_count != 25:
        raise RuntimeError(
            f"expected 25 standalone Complex.conj occurrences, found {conj_count}"
        )
    text = standalone_conj.sub("star", text)

    output_sha = sha256_text(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass317 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass317] FunctionalAnalysis namespace, subtype, and current-API frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
