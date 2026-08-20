from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    actual = text.count(old)
    if actual != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {actual}")
    print(f"{label}: applied {actual}")
    return text.replace(old, new)


def main() -> int:
    text = FA.read_text(encoding="utf-8")
    text = replace_exact(text, 'noncomputable local instance graphRangeModule : Module ℂ Q.GraphRange :=\n  Q.graphRangeInnerProductSpace.toModule\n\nnoncomputable local instance graphRangeNormedSpace : NormedSpace ℂ Q.GraphRange :=\n  Q.graphRangeInnerProductSpace.toNormedSpace\n\nnoncomputable local instance graphRangeInner : Inner ℂ Q.GraphRange :=\n  Q.graphRangeInnerProductSpace.toInner\n\nnoncomputable local instance graphRangeInnerProductSpaceInstance :\n    InnerProductSpace ℂ Q.GraphRange :=\n  Q.graphRangeInnerProductSpace\n\n', "/-- Use Mathlib's canonical subtype instances for all bundled maps and the\ncompletion.  The stored structure above remains available as a named API value,\nbut it is deliberately not installed as a second local instance. -/\n\n", 'FunctionalAnalysis remove duplicate graph-range instances', expected=1)
    text = replace_exact(text, '    (by\n      rw [UniformSpace.Completion.coe_toComplL]\n      exact UniformSpace.Completion.isUniformInducing_coe Q.GraphRange) x\n', '    (by\n      simpa only [UniformSpace.Completion.coe_toComplL] using\n        (UniformSpace.Completion.isUniformInducing_coe Q.GraphRange)) x\n', 'FunctionalAnalysis identify canonical completion embedding', expected=1)
    text = replace_exact(text, '  simpa [paperFourCoreMap] using\n    (paperFourCoordinates A J).denseRange_sectionCoreMap\n', '  simpa [PaperHalfWeightSobolevCompletion, paperFourCoreMap] using\n    (paperFourCoordinates A J).denseRange_sectionCoreMap\n', 'FunctionalAnalysis unfold page-four completion in dense range', expected=1)
    text = replace_exact(text, '  simpa [paperFourCoreMap] using h\n', '  simpa [PaperHalfWeightSobolevCompletion, paperFourCoreMap] using h\n', 'FunctionalAnalysis unfold page-four completion in injectivity', expected=1)
    text = replace_exact(text, 'open FixedPhasePeterssonCoordinates\n\n/-- The three concrete shifted Petersson coordinates on the canonical\n', 'open FixedPhasePeterssonCoordinates\n\n/-- `InverseEtaFixedPhaseCore` is an opaque noncomputable abbreviation of a\nsubmodule.  Re-export exactly the canonical subtype algebra structures at this\nboundary so the coordinate package does not invent a second module structure. -/\nnoncomputable local instance fixedPhaseCoreAddCommGroup (n : ℤ) :\n    AddCommGroup (InverseEtaFixedPhaseCore n) :=\n  inferInstanceAs\n    (AddCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n))\n\nnoncomputable local instance fixedPhaseCoreModule (n : ℤ) :\n    Module ℂ (InverseEtaFixedPhaseCore n) :=\n  inferInstanceAs\n    (Module ℂ (inverseEtaFixedPhaseStableCoreSubmodule n))\n\n/-- The three concrete shifted Petersson coordinates on the canonical\n', 'FunctionalAnalysis bridge canonical fixed-phase core algebra', expected=1)
    FA.write_text(text, encoding="utf-8")
    print("[pass313] FunctionalAnalysis canonical-instance frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
