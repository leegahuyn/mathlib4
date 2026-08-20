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
    text = replace_exact(
        text,
        'private theorem denseRange_energyCompletionMap_of_denseRange\n    (f : E →ₗᵢ[ℂ] F) (hf : DenseRange f) :\n    DenseRange (energyCompletionMap f) := by\n  apply DenseRange.of_comp (g := ((↑) : E → UniformSpace.Completion E))\n  have hcoe : Continuous ((↑) : F → UniformSpace.Completion F) :=\n    UniformSpace.Completion.continuous_coe\n  have h :\n      DenseRange (((↑) : F → UniformSpace.Completion F) ∘ (f : E → F)) :=\n    (UniformSpace.Completion.denseRange_coe :\n      DenseRange ((↑) : F → UniformSpace.Completion F)).comp hf hcoe\n  simpa only [Function.comp_apply, energyCompletionMap_coe] using h\n',
        'private theorem denseRange_energyCompletionMap_of_denseRange\n    (f : E →ₗᵢ[ℂ] F) (hf : DenseRange f) :\n    DenseRange (energyCompletionMap f) := by\n  apply DenseRange.of_comp (g := ((↑) : E → UniformSpace.Completion E))\n  have hcoe : Continuous ((↑) : F → UniformSpace.Completion F) :=\n    UniformSpace.Completion.continuous_coe (α := F)\n  have h :\n      DenseRange (((↑) : F → UniformSpace.Completion F) ∘ (f : E → F)) :=\n    (UniformSpace.Completion.denseRange_coe :\n      DenseRange ((↑) : F → UniformSpace.Completion F)).comp hf hcoe\n  change DenseRange (fun x : E =>\n    energyCompletionMap f (x : UniformSpace.Completion E))\n  rw [show\n    (fun x : E => energyCompletionMap f (x : UniformSpace.Completion E)) =\n      (fun x : E => (f x : UniformSpace.Completion F)) by\n        funext x\n        exact energyCompletionMap_coe f x]\n  exact h\n',
        "FunctionalAnalysis identify dense completion-map range without universe coercion",
    )
    FA.write_text(text, encoding="utf-8")
    print("[pass315] FunctionalAnalysis completion-map dense-range bridge repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
