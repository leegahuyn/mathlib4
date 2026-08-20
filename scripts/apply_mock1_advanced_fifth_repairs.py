from __future__ import annotations

import re
from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")


def mem_term(index: int) -> str:
    term = "List.Mem.head _"
    for _ in range(index):
        term = f"List.Mem.tail _ ({term})"
    return term


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied/source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def enum_mem_all(text: str, typ: str, cases: list[str]) -> tuple[str, bool]:
    pattern = re.compile(
        rf"theorem mem_all \((\w+) : {typ}\) :\n"
        rf"    List\.Mem \1 all := by\n"
        rf"(?:  classical\n)?  cases \1 <;> simp \[all\]\n"
    )
    var = "item" if typ != "IntegratedLayer" else "layer"
    lines = [f"theorem mem_all ({var} : {typ}) :", f"    List.Mem {var} all := by", f"  cases {var} with"]
    for i, c in enumerate(cases):
        lines.append(f"  | {c} => exact {mem_term(i)}")
    repaired, n = pattern.subn("\n".join(lines) + "\n", text, count=1)
    if n:
        print(f"Mock1Advanced {typ}.mem_all: applied")
    return repaired, bool(n)


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    for typ, cases in [
        ("ObjectiveItem", ["domainModel", "qSeriesPrincipal", "appellLerchBlock", "xiOperator",
          "slashAction", "linearPrincipalSystem", "entropyAsymptotic", "rademacherData",
          "degeneracyChannel", "effectiveCardyConstant", "sptEqualizer", "torObstruction",
          "padicMahler", "regressionCertificate", "abstractConcreteSeparation"]),
        ("RequestedDefinitionItem", ["domainQCusps", "qSeriesPrincipalPolar", "appellLerchSpecialization",
          "completionMuHatShadow", "xiOperator", "slashTransportMultiplier", "principalLinearSystems",
          "entropyAsymptotic", "rademacherExpansion", "degeneracyChannel", "effectiveCardyConstant",
          "sptEqualizerCrt", "torObstruction", "padicMahler", "regressionCertificate",
          "abstractConcreteSeparation"]),
        ("IntegratedLayer", ["basic", "spt", "muKernel", "rademacher", "pAdic", "regression", "advanced"]),
    ]:
        text, did = enum_mem_all(text, typ, cases)
        changed |= did

    old = """theorem primaryRequirement_mem_requiredKeys
    (layer : AxiomAuditLayer) :
    List.Mem (primaryRequirement layer) (requiredKeys layer) := by
  classical
  cases layer <;> simp [primaryRequirement, requiredKeys]
"""
    new = """theorem primaryRequirement_mem_requiredKeys
    (layer : AxiomAuditLayer) :
    List.Mem (primaryRequirement layer) (requiredKeys layer) := by
  cases layer <;> exact List.Mem.head _
"""
    text, did = replace_once(text, old, new, "Mock1Advanced primary requirement membership")
    changed |= did

    objective_positions = {
      "domainModel": ("basic", 0), "qSeriesPrincipal": ("basic", 1),
      "appellLerchBlock": ("muKernel", 0), "xiOperator": ("muKernel", 1),
      "slashAction": ("basic", 2), "linearPrincipalSystem": ("basic", 3),
      "entropyAsymptotic": ("basic", 4), "rademacherData": ("rademacher", 0),
      "degeneracyChannel": ("basic", 5), "effectiveCardyConstant": ("basic", 6),
      "sptEqualizer": ("spt", 0), "torObstruction": ("spt", 1),
      "padicMahler": ("pAdic", 0), "regressionCertificate": ("regression", 0),
      "abstractConcreteSeparation": ("advanced", 0),
    }
    pattern = re.compile(
        r"theorem exists_layer_for_objective \(item : ObjectiveItem\) :\n"
        r"    exists layer : IntegratedLayer,\n"
        r"      List\.Mem item \(objectives layer\) := by\n"
        r"(?:  classical\n)?(?:  cases item[\s\S]*?)(?=\n\ntheorem objective_covered)"
    )
    lines = ["theorem exists_layer_for_objective (item : ObjectiveItem) :",
             "    exists layer : IntegratedLayer,",
             "      List.Mem item (objectives layer) := by",
             "  cases item with"]
    for case, (layer, idx) in objective_positions.items():
        lines.append(f"  | {case} => exact Exists.intro IntegratedLayer.{layer} (by exact {mem_term(idx)})")
    text2, n = pattern.subn("\n".join(lines), text, count=1)
    if n:
        text = text2; changed = True
        print("Mock1Advanced objective layer witnesses: applied")

    old = """theorem primaryObjective_mem_integratedLayer_objectives
    (item : RequestedDefinitionItem) :
    List.Mem (primaryObjective item)
      (IntegratedLayer.objectives (integratedLayer item)) := by
  cases item <;> simp [integratedLayer, primaryObjective,
    IntegratedLayer.objectives]
"""
    request_positions = [0,1,0,0,1,2,3,4,0,5,6,0,1,0,0,0]
    request_cases = ["domainQCusps", "qSeriesPrincipalPolar", "appellLerchSpecialization",
      "completionMuHatShadow", "xiOperator", "slashTransportMultiplier", "principalLinearSystems",
      "entropyAsymptotic", "rademacherExpansion", "degeneracyChannel", "effectiveCardyConstant",
      "sptEqualizerCrt", "torObstruction", "padicMahler", "regressionCertificate",
      "abstractConcreteSeparation"]
    lines = ["theorem primaryObjective_mem_integratedLayer_objectives",
             "    (item : RequestedDefinitionItem) :",
             "    List.Mem (primaryObjective item)",
             "      (IntegratedLayer.objectives (integratedLayer item)) := by",
             "  cases item with"]
    for case, idx in zip(request_cases, request_positions):
        lines.append(f"  | {case} => exact {mem_term(idx)}")
    text, did = replace_once(text, old, "\n".join(lines) + "\n",
        "Mock1Advanced requested objective membership")
    changed |= did

    text2, n = re.subn(
        r"theorem reference_integrated_file_manifest\s*:\n\s*IntegratedFileManifest\s*:=",
        "def reference_integrated_file_manifest :\n    IntegratedFileManifest :=",
        text, count=1)
    if n:
        text = text2; changed = True
        print("Mock1Advanced manifest value declaration: changed theorem to def")

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
