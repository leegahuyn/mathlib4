from __future__ import annotations

import re
from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def write_if_changed(path: Path, old_text: str, new_text: str) -> None:
    if new_text != old_text:
        path.write_text(new_text, encoding="utf-8", newline="\n")


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    original = text

    patterns = [
        (r"(theorem primaryRequirement_mem_requiredKeys[\s\S]*? := by)\n  cases layer",
         r"\1\n  classical\n  cases layer"),
        (r"(theorem mem_all \(item : ObjectiveItem\)[\s\S]*? := by)\n  cases item",
         r"\1\n  classical\n  cases item"),
        (r"(theorem mem_all \(item : RequestedDefinitionItem\)[\s\S]*? := by)\n  cases item",
         r"\1\n  classical\n  cases item"),
        (r"(theorem mem_all \(layer : IntegratedLayer\)[\s\S]*? := by)\n  cases layer",
         r"\1\n  classical\n  cases layer"),
        (r"(theorem exists_layer_for_objective[\s\S]*? := by)\n  cases item",
         r"\1\n  classical\n  cases item"),
    ]
    for pattern, replacement in patterns:
        text, _ = re.subn(pattern, replacement, text, count=1)

    text = text.replace(
        "effectiveCardyConstant B.checklist.entropyWitness.alpha",
        "MockCert.effectiveCardyConstant B.checklist.entropyWitness.alpha",
    )
    write_if_changed(path, original, text)


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    original = text

    text = text.replace(
"""  apply AddCommGrpCat.hom_ext
  simpa [intersectionInclusion, comparison] using
    (Phi_comp_intersectionIdealIncl_eq_zero M N)
""",
"""  apply AddCommGrpCat.hom_ext
  change (Phi M N).comp (intersectionIdealIncl M N) = 0
  exact Phi_comp_intersectionIdealIncl_eq_zero M N
""", 1)
    text = text.replace(
"""  apply AddCommGrpCat.hom_ext
  simpa [comparison, difference] using (psi_comp_Phi_eq_zero M N)
""",
"""  apply AddCommGrpCat.hom_ext
  change (psi M N).comp (Phi M N) = 0
  exact psi_comp_Phi_eq_zero M N
""", 1)
    text = text.replace(
"""    apply intersectionIdealIncl_injective M N
    simpa using hx
""",
"""    apply intersectionIdealIncl_injective M N
    simpa only [map_zero] using hx
""", 1)
    write_if_changed(path, original, text)


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    original = text

    marker = "theorem hyperbolicMeasure_def :"
    if marker in text and "set_option maxHeartbeats 800000 in\n" + marker not in text:
        text = text.replace(marker, "set_option maxHeartbeats 800000 in\n" + marker, 1)

    text = text.replace(
"""  change
    -(Real.pi * (n : ℝ) * τ.im * 2) - Real.pi * (n : ℝ) ^ 2 * τ.im - Real.pi * τ.im =
      -(Real.pi * (n : ℝ) * τ.im * 2) - Real.pi * (n : ℝ) ^ 2 * τ.im - Real.pi * τ.im
  rfl
""", "  ring\n", 1)
    text = text.replace(
"""  apply hclosure
  simpa only [Submodule.topologicalClosure_coe] using u.property
""",
"""  apply hclosure
  change (u : H) ∈ closure (↑M.core : Set H)
  simpa only [Submodule.topologicalClosure_coe] using u.property
""", 1)
    text = text.replace(
"""  intro u v huv
  apply Subtype.ext
  apply M.toFunction_injective
  simpa [trialToAEAutomorphic] using congrArg Subtype.val huv
""",
"""  intro u v huv
  apply Subtype.ext
  apply M.toFunction_injective
  have hfun := congrArg Subtype.val huv
  change M.toFunction (u : H) = M.toFunction (v : H) at hfun
  exact hfun
""", 1)
    text = text.replace("refine Set.disjoint_left.mpr fun τ h∞ h₀ => ?_",
                        "refine Set.disjoint_left.mpr (fun τ h∞ h₀ => ?_)")
    text = text.replace("refine Set.disjoint_left.mpr fun τ h∞ h₁ => ?_",
                        "refine Set.disjoint_left.mpr (fun τ h∞ h₁ => ?_)")
    text = text.replace("refine Set.disjoint_left.mpr fun τ h₀ h₁ => ?_",
                        "refine Set.disjoint_left.mpr (fun τ h₀ h₁ => ?_)")
    text = text.replace(
        "Pairwise (Disjoint on strictCuspHoroball)",
        "Pairwise (fun κ λ => Disjoint (strictCuspHoroball κ) (strictCuspHoroball λ))",
        1,
    )
    write_if_changed(path, original, text)


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    original = text

    text = text.replace("set_option maxRecDepth 2000 in\n", "set_option maxRecDepth 10000 in\n")
    text = text.replace(
"""    have hv := congrArg (fun G : StrongAntiDual V => G v) hshift
    change (B u) v + (lam : ℂ) * (mass u) v = F v
    exact hv
""",
"""    have hv := congrArg (fun G : StrongAntiDual V => G v) hshift
    change (B u) v + (lam : ℂ) * (mass u) v = F v at hv
    exact hv
""", 1)
    write_if_changed(path, original, text)


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
