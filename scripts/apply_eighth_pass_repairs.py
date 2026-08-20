from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")

OLD_BLOCK = """def requestedDefinitions : IntegratedLayer -> List RequestedDefinitionItem
  | basic =>
      [RequestedDefinitionItem.domainQCusps,
        RequestedDefinitionItem.qSeriesPrincipalPolar,
        RequestedDefinitionItem.slashTransportMultiplier,
        RequestedDefinitionItem.principalLinearSystems,
        RequestedDefinitionItem.entropyAsymptotic,
        RequestedDefinitionItem.degeneracyChannel,
        RequestedDefinitionItem.effectiveCardyConstant]
  | spt =>
      [RequestedDefinitionItem.sptEqualizerCrt,
        RequestedDefinitionItem.torObstruction]
  | muKernel =>
      [RequestedDefinitionItem.appellLerchSpecialization,
        RequestedDefinitionItem.completionMuHatShadow,
        RequestedDefinitionItem.xiOperator]
  | rademacher =>
      [RequestedDefinitionItem.rademacherExpansion]
  | pAdic =>
      [RequestedDefinitionItem.padicMahler]
  | regression =>
      [RequestedDefinitionItem.regressionCertificate]
  | advanced =>
      [RequestedDefinitionItem.abstractConcreteSeparation]

theorem requestedDefinitions_length_pos
    (layer : IntegratedLayer) :
    0 < (requestedDefinitions layer).length := by
  cases layer <;> simp [requestedDefinitions]

theorem requestedDefinition_layer_sound
    (layer : IntegratedLayer) (item : RequestedDefinitionItem)
    (hmem : List.Mem item (requestedDefinitions layer)) :
    RequestedDefinitionItem.integratedLayer item = layer := by
  cases layer <;> cases item <;>
    simp_all only [requestedDefinitions, RequestedDefinitionItem.integratedLayer,
      List.mem_cons, List.not_mem_nil]

theorem requestedDefinition_objective_sound
    (layer : IntegratedLayer) (item : RequestedDefinitionItem)
    (hmem : List.Mem item (requestedDefinitions layer)) :
    List.Mem (RequestedDefinitionItem.primaryObjective item)
      (objectives layer) := by
  cases layer <;> cases item <;>
    simp_all only [requestedDefinitions, RequestedDefinitionItem.primaryObjective,
      objectives, List.mem_cons, List.not_mem_nil]

theorem requestedDefinition_mem_integratedLayer
    (item : RequestedDefinitionItem) :
    List.Mem item
      (requestedDefinitions (RequestedDefinitionItem.integratedLayer item)) := by
  cases item <;>
    decide
"""

NEW_BLOCK = """def requestedDefinitions (layer : IntegratedLayer) :
    List RequestedDefinitionItem :=
  RequestedDefinitionItem.all.filter fun item =>
    RequestedDefinitionItem.integratedLayer item = layer

theorem requestedDefinitions_length_pos
    (layer : IntegratedLayer) :
    0 < (requestedDefinitions layer).length := by
  cases layer with
  | basic =>
      have h := RequestedDefinitionItem.mem_all
        RequestedDefinitionItem.domainQCusps
      exact List.length_pos.mpr
        (List.mem_filter.mpr ⟨h, by simp⟩)
  | spt =>
      have h := RequestedDefinitionItem.mem_all
        RequestedDefinitionItem.sptEqualizerCrt
      exact List.length_pos.mpr
        (List.mem_filter.mpr ⟨h, by simp⟩)
  | muKernel =>
      have h := RequestedDefinitionItem.mem_all
        RequestedDefinitionItem.appellLerchSpecialization
      exact List.length_pos.mpr
        (List.mem_filter.mpr ⟨h, by simp⟩)
  | rademacher =>
      have h := RequestedDefinitionItem.mem_all
        RequestedDefinitionItem.rademacherExpansion
      exact List.length_pos.mpr
        (List.mem_filter.mpr ⟨h, by simp⟩)
  | pAdic =>
      have h := RequestedDefinitionItem.mem_all
        RequestedDefinitionItem.padicMahler
      exact List.length_pos.mpr
        (List.mem_filter.mpr ⟨h, by simp⟩)
  | regression =>
      have h := RequestedDefinitionItem.mem_all
        RequestedDefinitionItem.regressionCertificate
      exact List.length_pos.mpr
        (List.mem_filter.mpr ⟨h, by simp⟩)
  | advanced =>
      have h := RequestedDefinitionItem.mem_all
        RequestedDefinitionItem.abstractConcreteSeparation
      exact List.length_pos.mpr
        (List.mem_filter.mpr ⟨h, by simp⟩)

theorem requestedDefinition_layer_sound
    (layer : IntegratedLayer) (item : RequestedDefinitionItem)
    (hmem : List.Mem item (requestedDefinitions layer)) :
    RequestedDefinitionItem.integratedLayer item = layer :=
  of_decide_eq_true (List.mem_filter.mp hmem).2

theorem requestedDefinition_objective_sound
    (layer : IntegratedLayer) (item : RequestedDefinitionItem)
    (hmem : List.Mem item (requestedDefinitions layer)) :
    List.Mem (RequestedDefinitionItem.primaryObjective item)
      (objectives layer) := by
  have hlayer := requestedDefinition_layer_sound layer item hmem
  rw [← hlayer]
  exact RequestedDefinitionItem.primaryObjective_mem_integratedLayer_objectives item

theorem requestedDefinition_mem_integratedLayer
    (item : RequestedDefinitionItem) :
    List.Mem item
      (requestedDefinitions (RequestedDefinitionItem.integratedLayer item)) :=
  List.mem_filter.mpr ⟨RequestedDefinitionItem.mem_all item, by simp⟩
"""


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    count = text.count(OLD_BLOCK)
    if count == 0:
        print("Mock1Advanced structural requested-definition placement: already applied/source changed")
        return 0
    if count != 1:
        raise RuntimeError(
            f"Mock1Advanced requested-definition block: expected one match, found {count}")
    PATH.write_text(text.replace(OLD_BLOCK, NEW_BLOCK),
                    encoding="utf-8", newline="\n")
    print("Mock1Advanced structural requested-definition placement: applied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
