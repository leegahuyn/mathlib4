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

    text, did = replace_once(
        text,
        """  mock1ShadowZero :
    forall {X : Type*} (xiFhat g : X -> Complex) (S kappa : Complex),
""",
        """  mock1ShadowZero :
    forall {X : Type} (xiFhat g : X -> Complex) (S kappa : Complex),
""",
        "Mock1Advanced fix the concrete completion-ledger shadow universe")
    changed |= did

    text, did = replace_once(
        text,
        """theorem mock1_shadow_zero_at
    (L : RequirementCompletionLedger)
    {X : Type*} (xiFhat g : X -> Complex) (S kappa : Complex)
""",
        """theorem mock1_shadow_zero_at
    (L : RequirementCompletionLedger)
    {X : Type} (xiFhat g : X -> Complex) (S kappa : Complex)
""",
        "Mock1Advanced align the completion-ledger shadow accessor")
    changed |= did

    data_declarations = [
        ("def referenceRequirementCompletionLedger :\n    RequirementCompletionLedger where",
         "noncomputable def referenceRequirementCompletionLedger :\n    RequirementCompletionLedger.{0} where",
         "Mock1Advanced make the reference completion ledger concrete data"),
        ("theorem reference_requirement_completion_ledger :\n    RequirementCompletionLedger :=",
         "noncomputable def reference_requirement_completion_ledger :\n    RequirementCompletionLedger.{0} :=",
         "Mock1Advanced make the completion-ledger alias concrete data"),
        ("theorem reference_paper_module_registry :\n    PaperModuleRegistry :=",
         "def reference_paper_module_registry :\n    PaperModuleRegistry :=",
         "Mock1Advanced make the paper module registry alias data"),
        ("theorem reference_paper_data_consistency_schema :\n    PaperDataConsistencySchema :=",
         "def reference_paper_data_consistency_schema :\n    PaperDataConsistencySchema :=",
         "Mock1Advanced make the paper data schema alias data"),
        ("theorem module_registry_at (P : PaperProtocolCertificate) :\n    PaperModuleRegistry :=",
         "def module_registry_at (P : PaperProtocolCertificate) :\n    PaperModuleRegistry :=",
         "Mock1Advanced make protocol module-registry projection data"),
        ("theorem data_schema_at (P : PaperProtocolCertificate) :\n    PaperDataConsistencySchema :=",
         "def data_schema_at (P : PaperProtocolCertificate) :\n    PaperDataConsistencySchema :=",
         "Mock1Advanced make protocol data-schema projection data"),
        ("theorem reference_paper_protocol_certificate :\n    PaperProtocolCertificate :=",
         "def reference_paper_protocol_certificate :\n    PaperProtocolCertificate :=",
         "Mock1Advanced make the paper protocol alias data"),
    ]
    for old, new, label in data_declarations:
        text, did = replace_once(text, old, new, label)
        changed |= did

    text, did = replace_once(
        text,
        """theorem mem_all (m : PaperInfrastructureModule) :
    List.Mem m all := by
  cases m <;> simp [all]
""",
        """theorem mem_all (m : PaperInfrastructureModule) :
    List.Mem m all := by
  decide
""",
        "Mock1Advanced decide the closed paper-module membership table")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    zero_proofs = [
        ("""  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
""",
         """  comm₁₂ := by
    simp [Prop21StandardSequence.leftEndpoint,
      Prop21StandardSequence.zeroToIntersection]
""",
         "Mock2 unfold the left trivial short-complex square"),
        ("""  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact Subsingleton.elim _ _

/-- Naturality morphism for the short complex ending in the literal cokernel. -/
""",
         """  comm₂₃ := by
    simp [Prop21StandardSequence.rightEndpoint,
      Prop21StandardSequence.gcdToZero]

/-- Naturality morphism for the short complex ending in the literal cokernel. -/
""",
         "Mock2 unfold the standard right trivial square"),
        ("""  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact Subsingleton.elim _ _

/-- Auditable statement of the proven naturality range. -/
""",
         """  comm₂₃ := by
    simp [PhiCokernel.rightEndpoint, PhiCokernel.toZero]

/-- Auditable statement of the proven naturality range. -/
""",
         "Mock2 unfold the actual-cokernel right trivial square"),
    ]
    for old, new, label in zero_proofs:
        text, did = replace_once(text, old, new, label)
        changed |= did

    text, did = replace_once(
        text,
        """theorem Tor1Model_exp_IC (M N : ℕ) (hM : M ≠ 0) (hN : N ≠ 0) :
    (Fintype.card (Tor1Model M N) : ℝ) = Real.exp (IC M N) := by
  haveI : NeZero (Nat.gcd M N) := ⟨Nat.gcd_ne_zero_left hM⟩
  rw [Tor1Model_card, card_Tor_eq_exp_IC hM hN]
""",
        """theorem Tor1Model_exp_IC (M N : ℕ) (hM : M ≠ 0) (hN : N ≠ 0) :
    letI : NeZero (Nat.gcd M N) := ⟨Nat.gcd_ne_zero_left hM⟩
    (Fintype.card (Tor1Model M N) : ℝ) = Real.exp (IC M N) := by
  dsimp
  rw [Tor1Model_card, card_Tor_eq_exp_IC hM hN]
""",
        "Mock2 install the gcd nonzero instance in the theorem type")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ((1 / ENNReal.ofNNReal ⟨z.im, z.im_pos.le⟩) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    new = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        (↑((1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) ^ 2) : ENNReal) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    text, changed = replace_once(
        text, old, new,
        "Mock2Advanced match the canonical hyperbolic density exactly")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """        map_smul' := by
          intro r v
          have hr : r • v = (r : ℂ) • v := rfl
          simp only [hr, map_smulₛₗ, starRingEnd_apply, Complex.star_def,
            Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul] }
"""
    new = """        map_smul' := by
          intro r v
          have hr : r • v = (r : ℂ) • v := rfl
          rw [hr, map_smulₛₗ]
          simp only [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
            smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, sub_zero] }
"""
    text, did = replace_once(
        text, old, new,
        "FunctionalAnalysis prove real scalar compatibility by primitive components")
    changed |= did

    old = """      (by
        intro r u v
        have hr : r • v = (r : ℂ) • v := rfl
        simp only [hr, map_smulₛₗ, starRingEnd_apply, Complex.star_def,
          Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul])
"""
    new = """      (by
        intro r u v
        have hr : r • v = (r : ℂ) • v := rfl
        rw [hr, map_smulₛₗ]
        simp only [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
          smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero])
"""
    text, did = replace_once(
        text, old, new,
        "FunctionalAnalysis prove anti-linear form scalar compatibility componentwise")
    changed |= did

    text, did = replace_once(
        text,
        """theorem weakAntiEquation_of_forall_re_eq
    (B : ContinuousSesquilinearForm V) (u : V) (F : StrongAntiDual V)
""",
        """set_option maxHeartbeats 800000 in
theorem weakAntiEquation_of_forall_re_eq
    (B : ContinuousSesquilinearForm V) (u : V) (F : StrongAntiDual V)
""",
        "FunctionalAnalysis local heartbeat for the complex-equation recovery")
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
