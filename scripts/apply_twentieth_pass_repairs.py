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
        """structure UnconditionalCertificationReleaseEnvelope where
""",
        """universe uRelease

structure UnconditionalCertificationReleaseEnvelope where
""",
        "Mock1Advanced name the release-envelope universe")
    changed |= did

    text, did = replace_once(
        text,
        """  mock1ShadowZero :
    forall {X : Type*} (xiFhat g : X -> Complex) (S kappa : Complex),
""",
        """  mock1ShadowZero :
    forall {X : Type uRelease} (xiFhat g : X -> Complex) (S kappa : Complex),
""",
        "Mock1Advanced bind the release shadow theorem universe")
    changed |= did

    count = text.count("(R : UnconditionalCertificationReleaseEnvelope)")
    if count:
        text = text.replace(
            "(R : UnconditionalCertificationReleaseEnvelope)",
            "(R : UnconditionalCertificationReleaseEnvelope.{uRelease})")
        changed = True
        print(f"Mock1Advanced type release-envelope namespace parameters: applied {count}")

    text, did = replace_once(
        text,
        """theorem mock1_shadow_zero_at
    (R : UnconditionalCertificationReleaseEnvelope.{uRelease})
    {X : Type*} (xiFhat g : X -> Complex) (S kappa : Complex)
""",
        """theorem mock1_shadow_zero_at
    (R : UnconditionalCertificationReleaseEnvelope.{uRelease})
    {X : Type uRelease} (xiFhat g : X -> Complex) (S kappa : Complex)
""",
        "Mock1Advanced align release shadow accessor universe")
    changed |= did

    declaration_replacements = [
        ("theorem evidence_at\n", "noncomputable def evidence_at\n",
         "Mock1Advanced evidence projection is data"),
        ("theorem aggregation_at\n", "noncomputable def aggregation_at\n",
         "Mock1Advanced aggregation projection is data"),
        ("theorem mock1_compatibility_at\n", "noncomputable def mock1_compatibility_at\n",
         "Mock1Advanced compatibility projection is data"),
        ("theorem final_ledger_at\n", "noncomputable def final_ledger_at\n",
         "Mock1Advanced final-ledger projection is data"),
        ("theorem detail_ledger_at\n", "noncomputable def detail_ledger_at\n",
         "Mock1Advanced detail-ledger projection is data"),
        ("def referenceUnconditionalCertificationReleaseEnvelope :\n",
         "noncomputable def referenceUnconditionalCertificationReleaseEnvelope :\n",
         "Mock1Advanced reference release is noncomputable data"),
        ("theorem reference_unconditional_certification_release_envelope :\n",
         "noncomputable def reference_unconditional_certification_release_envelope :\n",
         "Mock1Advanced release alias is data"),
        ("theorem reference_release_aggregation :\n",
         "noncomputable def reference_release_aggregation :\n",
         "Mock1Advanced reference aggregation is data"),
        ("theorem reference_release_project_lock :\n",
         "noncomputable def reference_release_project_lock :\n",
         "Mock1Advanced reference project lock is data"),
        ("theorem reference_release_layer_blueprint :\n",
         "noncomputable def reference_release_layer_blueprint :\n",
         "Mock1Advanced reference layer blueprint is data"),
        ("theorem reference_release_mock1_compatibility :\n",
         "noncomputable def reference_release_mock1_compatibility :\n",
         "Mock1Advanced reference compatibility is data"),
        ("theorem release_at (L : RequirementCompletionLedger) :\n",
         "noncomputable def release_at (L : RequirementCompletionLedger) :\n",
         "Mock1Advanced ledger release projection is data"),
    ]
    for old, new, label in declaration_replacements:
        if old in text:
            text = text.replace(old, new, 1)
            changed = True
            print(f"{label}: applied")
        elif new in text:
            print(f"{label}: already applied")
        else:
            print(f"{label}: source changed; skipped")

    text, did = replace_once(
        text,
        """noncomputable def referenceUnconditionalCertificationReleaseEnvelope :
    UnconditionalCertificationReleaseEnvelope where
""",
        """noncomputable def referenceUnconditionalCertificationReleaseEnvelope :
    UnconditionalCertificationReleaseEnvelope.{0} where
""",
        "Mock1Advanced fix the concrete reference release universe")
    changed |= did

    text, did = replace_once(
        text,
        """noncomputable def reference_unconditional_certification_release_envelope :
    UnconditionalCertificationReleaseEnvelope :=
""",
        """noncomputable def reference_unconditional_certification_release_envelope :
    UnconditionalCertificationReleaseEnvelope.{0} :=
""",
        "Mock1Advanced fix the concrete release alias universe")
    changed |= did

    count = text.count("release : UnconditionalCertificationReleaseEnvelope\n")
    if count:
        text = text.replace(
            "release : UnconditionalCertificationReleaseEnvelope\n",
            "release : UnconditionalCertificationReleaseEnvelope.{0}\n")
        changed = True
        print(f"Mock1Advanced fix concrete ledger release universes: applied {count}")

    text, did = replace_once(
        text,
        """noncomputable def release_at (L : RequirementCompletionLedger) :
    UnconditionalCertificationReleaseEnvelope :=
""",
        """noncomputable def release_at (L : RequirementCompletionLedger) :
    UnconditionalCertificationReleaseEnvelope.{0} :=
""",
        "Mock1Advanced fix ledger release accessor universe")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_once(
        text,
        "def zeroObject : Ab := AddCommGrpCat.of (ZMod 1)",
        "abbrev zeroObject : Ab := AddCommGrpCat.of (ZMod 1)",
        "Mock2 expose the trivial additive-group object definitionally")
    changed |= did

    text, did = replace_once(
        text,
        "def Tor1Model (M N : ℕ) := ZMod (Nat.gcd M N)",
        "abbrev Tor1Model (M N : ℕ) := ZMod (Nat.gcd M N)",
        "Mock2 expose Tor1Model instances through its ZMod model")
    changed |= did

    text, did = replace_once(
        text,
        """/-- All Section 3.2 claims for arbitrary natural moduli, with no positivity or
coprimality assumptions. -/
structure Prop21Section32Certificate (M N : ℕ) : Prop where
""",
        """universe uSection32

/-- All Section 3.2 claims for arbitrary natural moduli, with no positivity or
coprimality assumptions. -/
structure Prop21Section32Certificate (M N : ℕ) : Prop where
""",
        "Mock2 name the Section 3.2 certificate universe")
    changed |= did

    text, did = replace_once(
        text,
        "  actual_quotient_cokernel : PhiCokernel.Certificate M N\n",
        "  actual_quotient_cokernel : PhiCokernel.Certificate.{uSection32} M N\n",
        "Mock2 preserve the quotient universal-property universe")
    changed |= did

    text, did = replace_once(
        text,
        """theorem prop21Section32_certificate (M N : ℕ) :
    Prop21Section32Certificate M N := by
""",
        """theorem prop21Section32_certificate (M N : ℕ) :
    Prop21Section32Certificate.{uSection32} M N := by
""",
        "Mock2 make the Section 3.2 constructor universe-polymorphic")
    changed |= did

    text, did = replace_once(
        text,
        "  standard_and_actual_cokernel : Prop21Section32Certificate M (Pk p k)\n",
        "  standard_and_actual_cokernel : Prop21Section32Certificate.{uSection32} M (Pk p k)\n",
        "Mock2 preserve the prime-power certificate universe")
    changed |= did

    text, did = replace_once(
        text,
        """theorem prop21PrimePowerSection32_certificate
    (M p k : ℕ) (hM : 1 ≤ M) (hp : Nat.Prime p) (hk : 1 ≤ k) :
    Prop21PrimePowerSection32Certificate M p k := by
""",
        """theorem prop21PrimePowerSection32_certificate
    (M p k : ℕ) (hM : 1 ≤ M) (hp : Nat.Prime p) (hk : 1 ≤ k) :
    Prop21PrimePowerSection32Certificate.{uSection32} M p k := by
""",
        "Mock2 make the prime-power Section 3.2 constructor universe-polymorphic")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ((1 / (↑(⟨z.im, z.im_pos.le⟩ : NNReal) : ENNReal)) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    new = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ((1 / ENNReal.ofNNReal ⟨z.im, z.im_pos.le⟩) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    text, changed = replace_once(
        text, old, new,
        "Mock2Advanced use the explicit NNReal-to-ENNReal embedding")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    old = "  set_option maxHeartbeats 800000 maxRecDepth 10000 in\n"
    new = "  set_option maxHeartbeats 800000 in\n  set_option maxRecDepth 10000 in\n"
    count = text.count(old)
    if count:
        text = text.replace(old, new)
        path.write_text(text, encoding="utf-8", newline="\n")
        print(f"FunctionalAnalysis nest local elaboration options correctly: applied {count}")
    else:
        print("FunctionalAnalysis nest local elaboration options correctly: already applied/source changed")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
