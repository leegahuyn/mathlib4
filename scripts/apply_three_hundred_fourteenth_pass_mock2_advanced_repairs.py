from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_once(text: str, old: str, new: str, label: str) -> str:
    old_count = text.count(old)
    new_count = text.count(new)
    print(f"{label}: expected=1 old={old_count} new={new_count}")
    if old_count == 1 and new_count == 0:
        print(f"{label}: before={old.splitlines()[0]!r}")
        print(f"{label}: after={new.splitlines()[0]!r}")
        return text.replace(old, new)
    if old_count == 0 and new_count == 1:
        print(f"{label}: already applied")
        return text
    raise RuntimeError(
        f"{label}: expected exactly one unrepaired or repaired occurrence, "
        f"found old={old_count}, new={new_count}"
    )


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    replacements = [
        (
            "      KernelEvidence (@p07_typedCurvature_correctedAndProved)\n",
            "      KernelEvidence (@p07_typedCurvature_correctedAndProved.{0, 0, 0, 0})\n",
            "Mock2 Advanced P0 typed-curvature evidence universes",
        ),
        (
            "      KernelEvidence\n        (@UnnumberedFormulaLedger.section7F_uniformMajorantConvergence_proved)\n",
            "      KernelEvidence\n        (@UnnumberedFormulaLedger.section7F_uniformMajorantConvergence_proved.{0, 0})\n",
            "Mock2 Advanced Section7 uniform-majorant evidence universes",
        ),
        (
            "      KernelEvidence (@p07_automorphicSeriesLimit_correctedAndProved)\n",
            "      KernelEvidence (@p07_automorphicSeriesLimit_correctedAndProved.{0})\n",
            "Mock2 Advanced P0 automorphic-series evidence universe",
        ),
        (
            "      KernelEvidence\n        (@CorrectedLemmas.CorrectedPropositions.FlatQTransport.QLocalSystem.connectionOfTrivialization_compatible)\n",
            "      KernelEvidence\n        (@CorrectedLemmas.CorrectedPropositions.FlatQTransport.QLocalSystem.connectionOfTrivialization_compatible.{0, 0})\n",
            "Mock2 Advanced Section7 trivialization-compatible evidence universes",
        ),
        (
            "      KernelEvidence (@p07_compactEmbeddingReplacement_correctedAndProved)\n",
            "      KernelEvidence (@p07_compactEmbeddingReplacement_correctedAndProved.{0, 0})\n",
            "Mock2 Advanced P0 compact-embedding evidence universes",
        ),
        (
            "      KernelEvidence\n        (@CorrectedLemmas.CorrectedPropositions.FlatQTransport.QLocalSystem.transport_unique_of_trivialization)\n",
            "      KernelEvidence\n        (@CorrectedLemmas.CorrectedPropositions.FlatQTransport.QLocalSystem.transport_unique_of_trivialization.{0, 0})\n",
            "Mock2 Advanced Section7 transport evidence universes",
        ),
        (
            "      KernelEvidence (@p08_chosenConnectionCompatible_correctedAndProved)\n",
            "      KernelEvidence (@p08_chosenConnectionCompatible_correctedAndProved.{0, 0})\n",
            "Mock2 Advanced P0 chosen-connection evidence universes",
        ),
        (
            "      KernelEvidence\n        (@UnnumberedFormulaLedger.equations6_1_to_6_18_variableGaugeCovariance_correctedAndProved)\n",
            "      KernelEvidence\n        (@UnnumberedFormulaLedger.equations6_1_to_6_18_variableGaugeCovariance_correctedAndProved.{0, 0})\n",
            "Mock2 Advanced Section7 variable-gauge evidence universes",
        ),
        (
            "      KernelEvidence (@balancedPresheafSection_existsUnique_gluing)\n",
            "      KernelEvidence (@balancedPresheafSection_existsUnique_gluing.{0, 0, 0})\n",
            "Mock2 Advanced Section7 balanced-gluing evidence universes",
        ),
        (
            "      KernelEvidence (@curvature_add_expansion)\n",
            "      KernelEvidence (@curvature_add_expansion.{0, 0})\n",
            "Mock2 Advanced P0 curvature-add evidence universes",
        ),
        (
            "      KernelEvidence (@curvature_zero)\n",
            "      KernelEvidence (@curvature_zero.{0, 0})\n",
            "Mock2 Advanced P0 curvature-zero evidence universes",
        ),
        (
            "      KernelEvidence (@p09_tensorRestriction_correctedAndProved)\n",
            "      KernelEvidence (@p09_tensorRestriction_correctedAndProved.{0, 0, 0})\n",
            "Mock2 Advanced P0 tensor-restriction evidence universes",
        ),
        (
            "      KernelEvidence (@p09_equalizer_correctedAndProved)\n",
            "      KernelEvidence (@p09_equalizer_correctedAndProved.{0, 0, 0})\n",
            "Mock2 Advanced P0 equalizer evidence universes",
        ),
        (
            "        CorrectedLemmas.CorrectedPropositions.SheafBridge.noUniversalObjectMap\n",
            "        CorrectedLemmas.CorrectedPropositions.SheafBridge.noUniversalObjectMap.{0}\n",
            "Mock2 Advanced P0 missing-target obstruction universe",
        ),
    ]
    for old, new, label in replacements:
        text = replace_once(text, old, new, label)
    TARGET.write_text(text, encoding="utf-8")
    print("[pass314] Mock2_Advanced remaining evidence universes repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())