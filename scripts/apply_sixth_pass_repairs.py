from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied/source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem requestedDefinition_layer_sound
    (layer : IntegratedLayer) (item : RequestedDefinitionItem)
    (hmem : List.Mem item (requestedDefinitions layer)) :
    RequestedDefinitionItem.integratedLayer item = layer := by
  cases layer <;> cases item <;>
    simpa [requestedDefinitions, RequestedDefinitionItem.integratedLayer]
      using hmem
"""
    new = """theorem requestedDefinition_layer_sound
    (layer : IntegratedLayer) (item : RequestedDefinitionItem)
    (hmem : List.Mem item (requestedDefinitions layer)) :
    RequestedDefinitionItem.integratedLayer item = layer := by
  cases layer <;> cases item <;>
    simp_all [requestedDefinitions, RequestedDefinitionItem.integratedLayer]
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced requested-definition layer soundness")
    changed |= did

    old = """theorem requestedDefinition_objective_sound
    (layer : IntegratedLayer) (item : RequestedDefinitionItem)
    (hmem : List.Mem item (requestedDefinitions layer)) :
    List.Mem (RequestedDefinitionItem.primaryObjective item)
      (objectives layer) := by
  cases layer <;> cases item <;>
    simpa [requestedDefinitions, RequestedDefinitionItem.primaryObjective,
      objectives] using hmem
"""
    new = """theorem requestedDefinition_objective_sound
    (layer : IntegratedLayer) (item : RequestedDefinitionItem)
    (hmem : List.Mem item (requestedDefinitions layer)) :
    List.Mem (RequestedDefinitionItem.primaryObjective item)
      (objectives layer) := by
  cases layer <;> cases item <;>
    simp_all [requestedDefinitions, RequestedDefinitionItem.primaryObjective,
      objectives]
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced requested-definition objective soundness")
    changed |= did

    old = """theorem requestedDefinition_mem_integratedLayer
    (item : RequestedDefinitionItem) :
    List.Mem item
      (requestedDefinitions (RequestedDefinitionItem.integratedLayer item)) := by
  cases item <;>
    simp [requestedDefinitions, RequestedDefinitionItem.integratedLayer]
"""
    new = """theorem requestedDefinition_mem_integratedLayer
    (item : RequestedDefinitionItem) :
    List.Mem item
      (requestedDefinitions (RequestedDefinitionItem.integratedLayer item)) := by
  cases item <;>
    simp [requestedDefinitions, RequestedDefinitionItem.integratedLayer]
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced requested-definition placement")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """set_option maxHeartbeats 2000000 in
/-- The concrete density formula for the hyperbolic measure. -/
theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ↑((1 / (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) ^ 2) :=
  UpperHalfPlane.volume_def
"""
    new = """/-- The concrete density formula for the hyperbolic measure. -/
theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ↑((1 / (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    text, did = replace_once(text, old, new,
        "Mock2Advanced hyperbolic volume definition")
    changed |= did

    old = """  apply hclosure
  change (u : H) ∈ closure (↑M.core : Set H)
  simpa [weightedAutomorphicSobolev, Submodule.topologicalClosure_coe] using u.property
"""
    new = """  apply hclosure
  change (u : H) ∈ M.core.topologicalClosure
  exact u.property
"""
    text, did = replace_once(text, old, new,
        "Mock2Advanced closed-core membership")
    changed |= did

    old = """  rw [Set.disjoint_left]
  intro τ h∞ h₀
"""
    new = """  apply Set.disjoint_left.mpr
  intro τ h∞ h₀
"""
    text, did = replace_once(text, old, new,
        "Mock2Advanced infinity-zero disjointness introduction")
    changed |= did

    old = """  rw [Set.disjoint_left]
  intro τ h∞ h₁
"""
    new = """  apply Set.disjoint_left.mpr
  intro τ h∞ h₁
"""
    text, did = replace_once(text, old, new,
        "Mock2Advanced infinity-one disjointness introduction")
    changed |= did

    if "  section : TopologicalSpace.Opens X → Submodule ℂ E\n" in text:
        text = text.replace("  section : TopologicalSpace.Opens X → Submodule ℂ E\n",
                            "  «section» : TopologicalSpace.Opens X → Submodule ℂ E\n", 1)
        changed = True
        print("Mock2Advanced escape LinearPresheaf.section field: applied")
    text = text.replace("    V ≤ U → section U →ₗ[ℂ] section V\n",
                        "    V ≤ U → «section» U →ₗ[ℂ] «section» V\n", 1)
    text = text.replace("(s : section U)", "(s : «section» U)")

    if "  include : TensorPresheafMorphism L M sheaf\n" in text:
        text = text.replace("  include : TensorPresheafMorphism L M sheaf\n",
                            "  «include» : TensorPresheafMorphism L M sheaf\n", 1)
        changed = True
        print("Mock2Advanced escape QGaugeVariableSheaf.include field: applied")
    text = text.replace("(include.app U s)", "(«include».app U s)")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    old = text
    text = text.replace("set_option maxRecDepth 10000\n",
                        "set_option maxRecDepth 100000\n", 1)
    if text != old:
        path.write_text(text, encoding="utf-8", newline="\n")
        print("FunctionalAnalysis global recursion budget: raised")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
