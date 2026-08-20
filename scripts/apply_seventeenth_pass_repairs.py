from __future__ import annotations

from pathlib import Path


ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """def requestedDefinitions (layer : IntegratedLayer) :
    List RequestedDefinitionItem :=
  RequestedDefinitionItem.all.filter fun item =>
    RequestedDefinitionItem.integratedLayer item = layer
"""
    new = """def requestedDefinitions (layer : IntegratedLayer) :
    List RequestedDefinitionItem :=
  RequestedDefinitionItem.all.filter fun item =>
    RequestedDefinitionItem.integratedLayer item = layer

private theorem requestedDefinitions_length_pos_of_mem
    {x : RequestedDefinitionItem} {xs : List RequestedDefinitionItem}
    (h : List.Mem x xs) : 0 < xs.length := by
  induction xs with
  | nil => cases h
  | cons _ _ => exact Nat.succ_pos _
"""
    text, did = replace_once(
        text, old, new,
        "Mock1Advanced positive list length from explicit membership")
    changed |= did

    old_term = "List.length_pos.mpr"
    new_term = "requestedDefinitions_length_pos_of_mem"
    count = text.count(old_term)
    if count:
        text = text.replace(old_term, new_term)
        changed = True
        print(f"Mock1Advanced replace removed List.length_pos API: applied {count}")
    else:
        print("Mock1Advanced replace removed List.length_pos API: already applied/source changed")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ↑((1 / (⟨z.im, z.im_pos.le⟩ : ℝ≥0)) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    new = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ↑((1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    text, changed = replace_once(
        text, old, new,
        "Mock2Advanced parse NNReal density type explicitly")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    for name in ["realifiedFunctionalLinear", "realifiedFormLinear"]:
        old = f"noncomputable def {name}"
        new = f"set_option maxHeartbeats 800000 in\nnoncomputable def {name}"
        count = text.count(old)
        if count == 0:
            if new in text:
                print(f"FunctionalAnalysis local heartbeat for {name}: already applied")
                continue
            print(f"FunctionalAnalysis local heartbeat for {name}: source changed; skipped")
            continue
        if count != 1:
            raise RuntimeError(
                f"FunctionalAnalysis local heartbeat for {name}: expected one match, found {count}")
        text = text.replace(old, new, 1)
        changed = True
        print(f"FunctionalAnalysis local heartbeat for {name}: applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
