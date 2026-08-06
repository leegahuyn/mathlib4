from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """@[simp]
theorem graphExtension_coe (x : Q.GraphRange) :
    Q.graphExtension (x : Q.SobolevCompletion) =
      (x : EnergyTarget H₀ HR HL) := by
  unfold graphExtension
  exact ContinuousLinearMap.extend_eq _
    (UniformSpace.Completion.denseRange_coe :
      DenseRange ((↑) : Q.GraphRange → Q.SobolevCompletion))
    (by simpa using
      UniformSpace.Completion.isUniformInducing_coe Q.GraphRange) x
""",
        """@[simp]
theorem graphExtension_coe (x : Q.GraphRange) :
    Q.graphExtension (x : Q.SobolevCompletion) =
      (x : EnergyTarget H₀ HR HL) := by
  unfold graphExtension
  exact ContinuousLinearMap.extend_eq _
    (UniformSpace.Completion.denseRange_coe :
      DenseRange ((↑) : Q.GraphRange → Q.SobolevCompletion))
    (by
      rw [UniformSpace.Completion.coe_toComplL]
      exact UniformSpace.Completion.isUniformInducing_coe Q.GraphRange) x
""",
        "FunctionalAnalysis rewrite uniform inducing along toComplL",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
