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

    text, did = replace_once(
        text,
        "  L.mock1ShadowZero xiFhat g S kappa hshadow hS\n",
        "  L.mock1ShadowZero (X := X) xiFhat g S kappa hshadow hS\n",
        "Mock1Advanced specify the completion-ledger shadow domain")
    changed |= did

    text, did = replace_once(
        text,
        """theorem mem_all (m : PaperInfrastructureModule) :
    List.Mem m all := by
  decide
""",
        """theorem mem_all (m : PaperInfrastructureModule) :
    List.Mem m all := by
  cases m <;> decide
""",
        "Mock1Advanced decide each closed paper-module case")
    changed |= did

    data_replacements = [
        ("theorem reference_paper_module_registry :\n", "def reference_paper_module_registry :\n",
         "Mock1Advanced paper module registry alias is data"),
        ("theorem reference_paper_data_consistency_schema :\n", "def reference_paper_data_consistency_schema :\n",
         "Mock1Advanced paper data schema alias is data"),
        ("theorem module_registry_at\n    (P : PaperProtocolCertificate) :\n", "def module_registry_at\n    (P : PaperProtocolCertificate) :\n",
         "Mock1Advanced protocol module registry projection is data"),
        ("theorem data_schema_at\n    (P : PaperProtocolCertificate) :\n", "def data_schema_at\n    (P : PaperProtocolCertificate) :\n",
         "Mock1Advanced protocol data schema projection is data"),
        ("theorem reference_paper_protocol_certificate :\n", "def reference_paper_protocol_certificate :\n",
         "Mock1Advanced protocol alias is data"),
        ("theorem completion_at (L : AdvancedPaperInfrastructureLedger) :\n", "def completion_at (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced completion projection is data"),
        ("theorem module_registry_at\n    (L : AdvancedPaperInfrastructureLedger) :\n", "def module_registry_at\n    (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced infrastructure module registry projection is data"),
        ("theorem data_schema_at\n    (L : AdvancedPaperInfrastructureLedger) :\n", "def data_schema_at\n    (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced infrastructure data schema projection is data"),
        ("theorem protocol_at (L : AdvancedPaperInfrastructureLedger) :\n", "def protocol_at (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced infrastructure protocol projection is data"),
        ("theorem end_to_end_evidence_at\n    (L : AdvancedPaperInfrastructureLedger) :\n", "noncomputable def end_to_end_evidence_at\n    (L : AdvancedPaperInfrastructureLedger) :\n",
         "Mock1Advanced end-to-end evidence projection is data"),
        ("theorem reference_advanced_paper_infrastructure_ledger :\n", "noncomputable def reference_advanced_paper_infrastructure_ledger :\n",
         "Mock1Advanced infrastructure ledger alias is data"),
        ("theorem reference_paper_infrastructure_protocol :\n", "noncomputable def reference_paper_infrastructure_protocol :\n",
         "Mock1Advanced infrastructure protocol alias is data"),
        ("theorem reference_paper_infrastructure_data_schema :\n", "noncomputable def reference_paper_infrastructure_data_schema :\n",
         "Mock1Advanced infrastructure schema alias is data"),
    ]
    for old, new, label in data_replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    for name in [
        "referenceAdvancedPaperInfrastructureLedger",
        "referencePrincipalPartData",
        "referencePaperObjectSchema",
        "referenceDiagnosticTable",
        "referenceVerificationProtocol",
        "referencePrincipalPartSolve",
        "referenceTransportedPrincipalPart",
    ]:
        old = f"def {name}"
        new = f"noncomputable def {name}"
        if old in text and new not in text:
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
        "Mock1Advanced rename the reserved numbered-label section field")
    changed |= did

    count = text.count("{ section :=")
    if count:
        text = text.replace("{ section :=", "{ paperSection :=")
        changed = True
        print(f"Mock1Advanced update numbered-label constructors: applied {count}")

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
    exact (Category.zero_comp _).symm
""",
         "Mock2 close the left zero-composition square"),
        ("""  comm₂₃ := by
    simp [Prop21StandardSequence.rightEndpoint,
      Prop21StandardSequence.gcdToZero]
""",
         """  comm₂₃ := by
    exact Category.comp_zero _
""",
         "Mock2 close the standard right zero-composition square"),
        ("""  comm₂₃ := by
    simp [PhiCokernel.rightEndpoint, PhiCokernel.toZero]
""",
         """  comm₂₃ := by
    exact Category.comp_zero _
""",
         "Mock2 close the cokernel right zero-composition square"),
        ("""    (Fintype.card (Tor1Model M N) : ℝ) = Real.exp (IC M N) := by
  dsimp
  rw [Tor1Model_card, card_Tor_eq_exp_IC hM hN]
""",
         """    (Fintype.card (Tor1Model M N) : ℝ) = Real.exp (IC M N) := by
  rw [Tor1Model_card, card_Tor_eq_exp_IC hM hN]
""",
         "Mock2 remove the no-op instance reduction"),
        ("""theorem quotientStepIntegerHom_gcd_eq_zero (M N : ℕ) :
    quotientStepIntegerHom M N (Nat.gcd M N : ℤ) = 0 := by
  change (quotientStep M N : ZMod N) *
    (Nat.gcd M N : ZMod N) = 0
  rw [← Nat.cast_mul, quotientStep_mul_gcd, ZMod.natCast_self]
""",
         """theorem quotientStepIntegerHom_gcd_eq_zero (M N : ℕ) :
    quotientStepIntegerHom M N (Nat.gcd M N : ℤ) = 0 := by
  rw [quotientStepIntegerHom_apply, ← Nat.cast_mul,
    quotientStep_mul_gcd, ZMod.natCast_self]
""",
         "Mock2 expose the quotient-step integer hom before calculation"),
        ("""  map_add' x y := by
    apply Subtype.ext
    simp
""",
         """  map_add' x y := by
    apply Subtype.ext
    exact map_add (quotientToAmbientHom M N) x y
""",
         "Mock2 inherit canonical quotient-map additivity directly"),
        ("""      (quotientStep M N : ZMod N) * (z : ZMod N) := by
  simp
""",
         """      (quotientStep M N : ZMod N) * (z : ZMod N) := by
  exact quotientToAmbientHom_intCast M N z
""",
         "Mock2 reuse the quotient representative formula"),
        ("""  rw [quotientToAmbientHom_intCast]
  change ((((quotientStep M N : ℕ) : ℤ) * q : ℤ) : ZMod N) =
    (z : ZMod N)
  simpa [hq]
""",
         """  rw [quotientToAmbientHom_intCast]
  exact_mod_cast hq.symm
""",
         "Mock2 cast the quotient-factor divisibility witness directly"),
        ("""    f = gcdToKernelHom M N := by
  ext x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
""",
         """    f = gcdToKernelHom M N := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
""",
         "Mock2 compare kernel homomorphisms before subtype extensionality"),
    ]
    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if "(coprime_div_gcd_div_gcd" in text:
        text = text.replace("(coprime_div_gcd_div_gcd", "(Nat.coprime_div_gcd_div_gcd", 1)
        changed = True
        print("Mock2 qualify the coprime quotient-factor theorem: applied")

    count = text.count(".map_zsmul 1 z")
    if count:
        text = text.replace(".map_zsmul 1 z", ".map_zsmul z 1")
        changed = True
        print(f"Mock2 correct map_zsmul argument order: applied {count}")

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
        "Mock2Advanced make the NNReal density embedding explicit")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """        map_smul' := by
          intro r v
          have hr : r • v = (r : ℂ) • v := rfl
          rw [hr, map_smulₛₗ]
          simp only [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
            smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero] }
"""
    new = """        map_smul' := by
          set_option maxHeartbeats 4000000 in
            set_option maxRecDepth 100000 in
              intro r v
              have hr : r • v = (r : ℂ) • v := rfl
              rw [hr, map_smulₛₗ]
              simp only [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
                smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
                Complex.ofReal_im, zero_mul, sub_zero] }
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis raise limits inside functional scalar proof")
    changed |= did

    old = """      (by
        intro r u v
        have hr : r • v = (r : ℂ) • v := rfl
        rw [hr, map_smulₛₗ]
        simp only [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
          smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero])
"""
    new = """      (by
        set_option maxHeartbeats 4000000 in
          set_option maxRecDepth 100000 in
            intro r u v
            have hr : r • v = (r : ℂ) • v := rfl
            rw [hr, map_smulₛₗ]
            simp only [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
              smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, zero_mul, sub_zero])
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis raise limits inside form scalar proof")
    changed |= did

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
  set_option maxHeartbeats 4000000 in
    set_option maxRecDepth 100000 in
      apply (weakAntiEquation_iff_forall B u F).2
      intro v
      apply complex_eq_of_re_eq_of_re_neg_I_mul_eq (h v)
      have hI := h (Complex.I • v)
      simpa only [map_smulₛₗ, starRingEnd_apply, Complex.star_def,
        Complex.conj_I, smul_eq_mul] using hI
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis move recovery limits into the proof")
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
