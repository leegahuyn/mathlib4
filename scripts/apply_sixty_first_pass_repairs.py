from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(text: str, old: str, new: str, expected: int, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == expected:
        print(f"{label}: applied {count}")
        return text.replace(old, new), True
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count == 0:
        print(f"{label}: source changed; skipped")
        return text, False
    raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")


def section_classifier(name: str, section: str, count: int) -> str:
    lines = [
        f"theorem sectionOf_{name}_at",
        "    (b : AdvancedClaimsIIPromptBullet)",
        f"    (h : List.Mem b {name}Bullets) :",
        f"    sectionOf b = Section.{section} := by",
        f"  simp only [{name}Bullets] at h",
    ]
    for _ in range(count):
        lines.append("  rcases List.mem_cons.mp h with rfl | h")
        lines.append("  · rfl")
    lines.append("  cases h")
    return "\n".join(lines)


def group_mem_all(name: str) -> str:
    return f"""theorem {name}_mem_all
    (b : AdvancedClaimsIIPromptBullet)
    (_h : List.Mem b {name}Bullets) :
    List.Mem b all :=
  mem_all b"""


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem mem_all
    (b : AdvancedClaimsIIPromptBullet) :
    List.Mem b all := by
  decide
"""
    new = """theorem mem_all
    (b : AdvancedClaimsIIPromptBullet) :
    List.Mem b all := by
  cases b <;> simp [all]
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock1Advanced prove prompt-bullet completeness by constructor cases",
    )
    changed |= did

    old = """  | entropyRepro =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | finalInstance =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))
"""
    new = """  | entropyRepro =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
"""
    prompt_ns = text.index("namespace AdvancedClaimsIIPromptBullet")
    pos = text.find(old, prompt_ns)
    if pos >= 0:
        text = text[:pos] + new + text[pos + len(old):]
        changed = True
        print("Mock1Advanced remove impossible finalInstance prompt-section branch: applied")
    elif new in text[prompt_ns:]:
        print("Mock1Advanced remove impossible finalInstance prompt-section branch: already applied")
    else:
        print("Mock1Advanced remove impossible finalInstance prompt-section branch: source changed; skipped")

    prompt_ns = text.index("namespace AdvancedClaimsIIPromptBullet")
    start = text.index("theorem sectionOf_objectSchema_at", prompt_ns)
    end_marker = "end AdvancedClaimsIIRequirement"
    end = text.index(end_marker, start) + len(end_marker)

    specs = [
        ("objectSchema", "objectSchema", 4),
        ("t1t5", "t1t5", 8),
        ("spt", "spt", 5),
        ("kernel", "kernel", 8),
        ("exact", "exactCoefficient", 7),
        ("pAdic", "pAdic", 10),
        ("entropy", "entropyRepro", 9),
    ]
    classifiers = "\n\n".join(section_classifier(*spec) for spec in specs)
    memberships = "\n\n".join(group_mem_all(spec[0]) for spec in specs)
    replacement = classifiers + "\n\n" + memberships + "\n\nend AdvancedClaimsIIPromptBullet"
    if text[start:end] != replacement:
        text = text[:start] + replacement + text[end:]
        changed = True
        print("Mock1Advanced restore prompt-bullet section classifiers and group coverage: applied")
    else:
        print("Mock1Advanced restore prompt-bullet section classifiers and group coverage: already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """    calc
      _ = Lp.compMeasurePreserving (chart.coord ∘ chart.coord.symm)
            (hcoord.comp hsymm) F := hcomp.symm
      _ = F := by
        convert Lp.compMeasurePreserving_id_apply F using 1
        funext x
        exact chart.coord.apply_symm_apply x
"""
    new = """    have hfun : (chart.coord ∘ chart.coord.symm) = id := by
      funext x
      exact chart.coord.apply_symm_apply x
    simpa only [hfun, Lp.compMeasurePreserving_id_apply] using hcomp.symm
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2Advanced simplify forward-backward Lp composition with dependent proof transport",
    )
    changed |= did

    old = """    calc
      _ = Lp.compMeasurePreserving (chart.coord.symm ∘ chart.coord)
            (hsymm.comp hcoord) u := hcomp.symm
      _ = u := by
        convert Lp.compMeasurePreserving_id_apply u using 1
        funext x
        exact chart.coord.symm_apply_apply x
"""
    new = """    have hfun : (chart.coord.symm ∘ chart.coord) = id := by
      funext x
      exact chart.coord.symm_apply_apply x
    simpa only [hfun, Lp.compMeasurePreserving_id_apply] using hcomp.symm
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2Advanced simplify backward-forward Lp composition with dependent proof transport",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """    exact (Complex.continuousAt_sqrt (Or.inr him)).comp hdenom
""",
        """    exact (Complex.continuousAt_sqrt (Or.inr him)).comp' hdenom
""",
        1,
        "FunctionalAnalysis compose square-root continuity with the subtype denominator",
    )
    changed |= did

    old = """    simpa [ModularForm.discriminant] using
      (SlashInvariantForm.slash_action_eqn''
        ModularForm.discriminantCuspForm
        (show (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨γ, rfl⟩) z)
"""
    new = """    simpa [CuspForm.discriminant, ModularForm.discriminant] using
      (SlashInvariantForm.slash_action_eqn''
        CuspForm.discriminant
        (show (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨γ, rfl⟩) z)
"""
    text, did = replace_exact(
        text, old, new, 1,
        "FunctionalAnalysis use the current discriminant cusp-form constant",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
