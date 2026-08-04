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

    count = text.count("RequirementCompletionLedger.{0}")
    if count:
        text = text.replace("RequirementCompletionLedger.{0}", "RequirementCompletionLedger")
        changed = True
        print(f"Mock1Advanced remove invalid completion-ledger universe arguments: applied {count}")

    old = """theorem mem_all (m : PaperInfrastructureModule) :
    List.Mem m all := by
  decide
"""
    new = """theorem mem_all (m : PaperInfrastructureModule) :
    List.Mem m all := by
  cases m <;> decide
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced decide each closed paper-module case")
    changed |= did

    data_replacements = [
        ("theorem completion_at (L : AdvancedPaperInfrastructureLedger) :\n",
         "def completion_at (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced completion projection is data"),
        ("theorem module_registry_at\n    (L : AdvancedPaperInfrastructureLedger) :\n",
         "def module_registry_at\n    (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced module registry projection is data"),
        ("theorem data_schema_at\n    (L : AdvancedPaperInfrastructureLedger) :\n",
         "def data_schema_at\n    (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced data schema projection is data"),
        ("theorem protocol_at (L : AdvancedPaperInfrastructureLedger) :\n",
         "def protocol_at (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced protocol projection is data"),
        ("theorem end_to_end_evidence_at\n    (L : AdvancedPaperInfrastructureLedger) :\n",
         "noncomputable def end_to_end_evidence_at\n    (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced evidence projection is data"),
        ("def referenceAdvancedPaperInfrastructureLedger :\n",
         "noncomputable def referenceAdvancedPaperInfrastructureLedger :\n",
         "Mock1Advanced reference infrastructure ledger is noncomputable data"),
        ("theorem reference_advanced_paper_infrastructure_ledger :\n",
         "noncomputable def reference_advanced_paper_infrastructure_ledger :\n",
         "Mock1Advanced reference infrastructure alias is data"),
        ("theorem reference_paper_infrastructure_protocol :\n",
         "def reference_paper_infrastructure_protocol :\n",
         "Mock1Advanced reference protocol alias is data"),
        ("theorem reference_paper_infrastructure_data_schema :\n",
         "def reference_paper_infrastructure_data_schema :\n",
         "Mock1Advanced reference data-schema alias is data"),
    ]
    for old, new, label in data_replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    for name in [
        "referencePrincipalPartData",
        "referencePaperObjectSchema",
        "referenceDiagnosticTable",
        "referenceVerificationProtocol",
        "referencePrincipalPartSolve",
        "referenceTransportedPrincipalPart",
    ]:
        old = f"def {name}"
        new = f"noncomputable def {name}"
        count = text.count(old)
        if count:
            text = text.replace(old, new, 1)
            changed = True
            print(f"Mock1Advanced mark {name} noncomputable: applied")

    text, did = replace_once(
        text,
        """structure NumberedPaperLabel where
  section : PaperSection
""",
        """structure NumberedPaperLabel where
  paperSection : PaperSection
""",
        "Mock1Advanced escape the reserved section field")
    changed |= did

    count = text.count("{ section :=")
    if count:
        text = text.replace("{ section :=", "{ paperSection :=")
        changed = True
        print(f"Mock1Advanced update numbered-label constructors: applied {count}")
    count = text.count(".section")
    if count:
        text = text.replace(".section", ".paperSection")
        changed = True
        print(f"Mock1Advanced update numbered-label projections: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        ("""  comm₁₂ := by
    simp [Prop21StandardSequence.leftEndpoint,
      Prop21StandardSequence.zeroToIntersection]
""",
         """  comm₁₂ := by
    simpa using (zero_comp
      (AddCommGrpCat.ofHom (intersectionRestriction hM hN)))
""",
         "Mock2 close the left zero square by zero_comp"),
        ("""  comm₂₃ := by
    simp [Prop21StandardSequence.rightEndpoint,
      Prop21StandardSequence.gcdToZero]
""",
         """  comm₂₃ := by
    simpa using (comp_zero
      (AddCommGrpCat.ofHom (gcdRestriction hM hN)))
""",
         "Mock2 close the standard right zero square by comp_zero"),
        ("""  comm₂₃ := by
    simp [PhiCokernel.rightEndpoint, PhiCokernel.toZero]
""",
         """  comm₂₃ := by
    simpa using (comp_zero
      (AddCommGrpCat.ofHom (cokernelMap hM hN)))
""",
         "Mock2 close the actual right zero square by comp_zero"),
        ("""    (Fintype.card (Tor1Model M N) : ℝ) = Real.exp (IC M N) := by
  dsimp
  rw [Tor1Model_card, card_Tor_eq_exp_IC hM hN]
""",
         """    (Fintype.card (Tor1Model M N) : ℝ) = Real.exp (IC M N) := by
  rw [Tor1Model_card, card_Tor_eq_exp_IC hM hN]
""",
         "Mock2 remove the no-op instance dsimp"),
    ]
    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        (↑((1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2) : ENNReal) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    new = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ENNReal.ofNNReal ((1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2) := by
  set_option maxHeartbeats 800000 in
    simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    text, changed = replace_once(text, old, new,
        "Mock2Advanced embed the completed NNReal density explicitly")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = "  set_option maxRecDepth 10000 in\n"
    new = "  set_option maxRecDepth 100000 in\n"
    count = text.count(old)
    if count:
        text = text.replace(old, new)
        changed = True
        print(f"FunctionalAnalysis raise local recursion depth: applied {count}")

    old = """set_option maxHeartbeats 800000 in
theorem weakAntiEquation_of_forall_re_eq
    (B : ContinuousSesquilinearForm V) (u : V) (F : StrongAntiDual V)
    (h : ∀ v : V, (B u v).re = (F v).re) :
    WeakAntiEquation B u F := by
  apply (weakAntiEquation_iff_forall B u F).2
  intro v
  apply complex_eq_of_re_eq_of_re_neg_I_mul_eq (h v)
  have hI := h (Complex.I • v)
  simpa only [map_smulₛₗ, starRingEnd_apply, Complex.star_def,
    Complex.conj_I, smul_eq_mul] using hI
"""
    new = """theorem weakAntiEquation_of_forall_re_eq
    (B : ContinuousSesquilinearForm V) (u : V) (F : StrongAntiDual V)
    (h : ∀ v : V, (B u v).re = (F v).re) :
    WeakAntiEquation B u F := by
  set_option maxHeartbeats 800000 maxRecDepth 100000 in
    apply (weakAntiEquation_iff_forall B u F).2
    intro v
    apply complex_eq_of_re_eq_of_re_neg_I_mul_eq (h v)
    have hI := h (Complex.I • v)
    simpa only [map_smulₛₗ, starRingEnd_apply, Complex.star_def,
      Complex.conj_I, smul_eq_mul] using hI
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis move the recovery budget inside the theorem proof")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
