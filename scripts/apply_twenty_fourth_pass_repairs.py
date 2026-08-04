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

    count = text.count("noncomputable noncomputable def")
    if count:
        text = text.replace("noncomputable noncomputable def", "noncomputable def")
        changed = True
        print(f"Mock1Advanced remove duplicated noncomputable modifiers: applied {count}")

    text, did = replace_once(
        text,
        """theorem all_length :
    all.length = 8 := by
  classical
  simp [targets]

theorem mem_all (r : PaperTablesFRequirement) :
    List.Mem r all := by
  cases r <;> simp [all]
""",
        """theorem all_length :
    all.length = 8 := by
  rfl

theorem mem_all (r : PaperTablesFRequirement) :
    List.Mem r all := by
  cases r with
  | parameterTableSchema => exact List.Mem.head _
  | residualTableSchema => exact List.Mem.tail _ (List.Mem.head _)
  | rationalPassFailIntervals =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | rowModeAnnotations =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | finiteTableRecheckBoundary =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
  | externalScriptListCertificate =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  | paperRowsConvertedIntoCert =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | rationalOnlyNumerics =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))
""",
        "Mock1Advanced close the eight-row paper-table registry structurally")
    changed |= did

    replacements = [
        ("""structure AppellLerchBlockLabel where
  claim : AdvancedClaim
  section : PaperSection
  theoremNumber : Option PaperTheoremNumber
  equationNumber : Option PaperEquationNumber
  section_eq :
    (AdvancedClaim.toNumberedLabel claim).section = section
""",
         """structure AppellLerchBlockLabel where
  claim : AdvancedClaim
  paperSection : PaperSection
  theoremNumber : Option PaperTheoremNumber
  equationNumber : Option PaperEquationNumber
  section_eq :
    (AdvancedClaim.toNumberedLabel claim).paperSection = paperSection
""",
         "Mock1Advanced escape Appell-Lerch section field"),
        ("""theorem section_at (L : AppellLerchBlockLabel) :
    (AdvancedClaim.toNumberedLabel L.claim).section = L.section :=
  L.section_eq
""",
         """theorem section_at (L : AppellLerchBlockLabel) :
    (AdvancedClaim.toNumberedLabel L.claim).paperSection = L.paperSection :=
  L.section_eq
""",
         "Mock1Advanced update Appell-Lerch section accessor"),
        ("""    (AdvancedClaim.toNumberedLabel I.blockLabel.claim).section =
      I.blockLabel.section :=
  I.blockLabel.section_at
""",
         """    (AdvancedClaim.toNumberedLabel I.blockLabel.claim).paperSection =
      I.blockLabel.paperSection :=
  I.blockLabel.section_at
""",
         "Mock1Advanced update Appell-Lerch evidence accessor"),
    ]
    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    count = text.count("  section := PaperSection.")
    if count:
        text = text.replace("  section := PaperSection.", "  paperSection := PaperSection.")
        changed = True
        print(f"Mock1Advanced update Appell-Lerch constructors: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    for old, new, label in [
        ("    exact (Category.zero_comp _).symm\n",
         "    exact (zero_comp _).symm\n",
         "Mock2 use the global zero_comp lemma"),
        ("    exact Category.comp_zero _\n",
         "    exact comp_zero _\n",
         "Mock2 use the global comp_zero lemma"),
    ]:
        count = text.count(old)
        if count:
            text = text.replace(old, new)
            changed = True
            print(f"{label}: applied {count}")

    old = """theorem quotientStepIntegerHom_gcd_eq_zero (M N : ℕ) :
    quotientStepIntegerHom M N (Nat.gcd M N : ℤ) = 0 := by
  rw [quotientStepIntegerHom_apply, ← Nat.cast_mul,
    quotientStep_mul_gcd, ZMod.natCast_self]
"""
    new = """theorem quotientStepIntegerHom_gcd_eq_zero (M N : ℕ) :
    quotientStepIntegerHom M N (Nat.gcd M N : ℤ) = 0 := by
  rw [quotientStepIntegerHom_apply]
  have h := congrArg (fun n : ℕ => (n : ZMod N))
    (quotientStep_mul_gcd M N)
  simpa only [Nat.cast_mul, Int.cast_natCast, ZMod.natCast_self] using h
"""
    text, did = replace_once(text, old, new,
        "Mock2 transport the quotient-step gcd identity through the cast")
    changed |= did

    old = """  rw [quotientToAmbientHom_intCast]
  exact_mod_cast hq.symm
"""
    new = """  rw [quotientToAmbientHom_intCast]
  simpa only [Int.cast_mul] using
    congrArg (fun t : ℤ => (t : ZMod N)) hq.symm
"""
    text, did = replace_once(text, old, new,
        "Mock2 transport the surjectivity factorization through the cast")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ENNReal.ofNNReal (((1 : NNReal) /
          (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2) := by
  set_option maxHeartbeats 800000 in
    simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    new = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    text, did = replace_once(text, old, new,
        "Mock2Advanced match UpperHalfPlane.volume_def exactly")
    changed |= did

    anchor = """abbrev TrialSpace
    {J : HalfWeightAutomorphyFactor} {μ : Measure UpperHalfPlane}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (M : WeightedSobolevDatum J μ H) : Type _ :=
  ↥(weightedAutomorphicSobolev M)

"""
    addition = anchor + """noncomputable local instance trialSpaceComplete
    {J : HalfWeightAutomorphyFactor} {μ : Measure UpperHalfPlane}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (M : WeightedSobolevDatum J μ H) : CompleteSpace (TrialSpace M) :=
  (isClosed_weightedAutomorphicSobolev M).completeSpace_coe

"""
    text, did = replace_once(text, anchor, addition,
        "Mock2Advanced install completeness of the closed trial space")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
