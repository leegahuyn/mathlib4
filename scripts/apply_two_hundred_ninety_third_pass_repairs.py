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
        """abbrev GraphRange :=
  LinearMap.range Q.graph

def toGraphRange : V →ₗ[ℂ] Q.GraphRange :=
""",
        """abbrev GraphRange :=
  LinearMap.range Q.graph

/-- A single stored inner-product structure whose parent projections are used
for all bundled maps on the graph range. -/
noncomputable def graphRangeInnerProductSpace :
    InnerProductSpace ℂ Q.GraphRange :=
  Submodule.innerProductSpace Q.GraphRange

local instance graphRangeModule : Module ℂ Q.GraphRange :=
  Q.graphRangeInnerProductSpace.toModule

local instance graphRangeNormedSpace : NormedSpace ℂ Q.GraphRange :=
  Q.graphRangeInnerProductSpace.toNormedSpace

local instance graphRangeInner : Inner ℂ Q.GraphRange :=
  Q.graphRangeInnerProductSpace.toInner

local instance graphRangeInnerProductSpaceInstance :
    InnerProductSpace ℂ Q.GraphRange :=
  Q.graphRangeInnerProductSpace

def toGraphRange : V →ₗ[ℂ] Q.GraphRange :=
""",
        "FunctionalAnalysis coherent graph-range instances",
    )
    fa = replace_exact(
        fa,
        """/-- The Definition 1 Sobolev space: completion of the genuine energy graph. -/
abbrev SobolevCompletion :=
  UniformSpace.Completion Q.GraphRange

/-- Canonical isometric embedding of the graph core into its completion. -/
""",
        """/-- The Definition 1 Sobolev space: completion of the genuine energy graph. -/
abbrev SobolevCompletion :=
  UniformSpace.Completion Q.GraphRange

/-- Store the canonical completion inner product once, then use its parent
module and normed-space structures for every later bundled map. -/
noncomputable def sobolevCompletionInnerProductSpace :
    InnerProductSpace ℂ Q.SobolevCompletion :=
  UniformSpace.Completion.innerProductSpace

local instance sobolevCompletionModule : Module ℂ Q.SobolevCompletion :=
  Q.sobolevCompletionInnerProductSpace.toModule

local instance sobolevCompletionNormedSpace :
    NormedSpace ℂ Q.SobolevCompletion :=
  Q.sobolevCompletionInnerProductSpace.toNormedSpace

local instance sobolevCompletionInner : Inner ℂ Q.SobolevCompletion :=
  Q.sobolevCompletionInnerProductSpace.toInner

local instance sobolevCompletionInnerProductSpaceInstance :
    InnerProductSpace ℂ Q.SobolevCompletion :=
  Q.sobolevCompletionInnerProductSpace

/-- Canonical isometric embedding of the graph core into its completion. -/
""",
        "FunctionalAnalysis coherent completion instances",
    )
    fa = replace_exact(
        fa,
        """  rw [Q.completionEnergyOperator_apply]
  change ⟪Q.coreEmbedding (Q.toGraphRange v),
      Q.coreEmbedding (Q.toGraphRange u)⟫_ℂ = Q.energyForm v u
  exact (Q.coreEmbedding.inner_map_map _ _).trans
    (Q.inner_toGraphRange v u)
""",
        """  rw [Q.completionEnergyOperator_apply]
  change ⟪(Q.toGraphRange v : Q.SobolevCompletion),
      (Q.toGraphRange u : Q.SobolevCompletion)⟫_ℂ = Q.energyForm v u
  rw [UniformSpace.Completion.inner_coe, Q.inner_toGraphRange]
""",
        "FunctionalAnalysis evaluate the completed core pairing by density",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
