from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def first_line(text: str) -> str:
    lines = text.splitlines()
    return lines[0] if lines else ""


def replace_exact(
    text: str,
    old: str,
    new: str,
    label: str,
    expected: int = 1,
) -> str:
    actual = text.count(old)
    print(
        f"{label}: expected={expected} actual={actual} "
        f"before={first_line(old)!r} after={first_line(new)!r}"
    )
    if actual != expected:
        raise RuntimeError(
            f"{label}: expected {expected} matches, found {actual}"
        )
    return text.replace(old, new)


def main() -> int:
    text = M2.read_text(encoding="utf-8")

    # Keep the public Proposition 15 certificate proof-valued.  The two
    # categorical universal-property witnesses are data, so proof-level
    # packaging records their existence with Nonempty rather than changing
    # the public certificate theorem into a data definition.
    text = replace_exact(
        text,
        """structure StandaloneZeroProfileCertificate
    (M N : ℕ) (hM : M ≠ 0) : Type 1 where
""",
        """structure StandaloneZeroProfileCertificate
    (M N : ℕ) (hM : M ≠ 0) : Prop where
""",
        "Mock2 restore standalone certificate to Prop",
    )
    text = replace_exact(
        text,
        """  source_equalizer_universal :
    ∀ (S : ShEq.{0, 0} ActualBase) (U : ActualOpens),
      IsLimit (sourceEqualizerFork S U)
  target_equalizer_universal :
    ∀ (S : ShEq.{0, 0} ActualBase) (U : ActualOpens),
      IsLimit (targetEqualizerFork S U)
""",
        """  source_equalizer_universal :
    ∀ (S : ShEq.{0, 0} ActualBase) (U : ActualOpens),
      Nonempty (IsLimit (sourceEqualizerFork S U))
  target_equalizer_universal :
    ∀ (S : ShEq.{0, 0} ActualBase) (U : ActualOpens),
      Nonempty (IsLimit (targetEqualizerFork S U))
""",
        "Mock2 proof-package equalizer limit witnesses",
    )
    text = replace_exact(
        text,
        "noncomputable def standaloneZeroProfile_certificate (M N : ℕ) (hM : M ≠ 0) :",
        "theorem standaloneZeroProfile_certificate (M N : ℕ) (hM : M ≠ 0) :",
        "Mock2 restore standalone certificate theorem",
    )
    text = replace_exact(
        text,
        """  source_equalizer_universal := sourceEqualizerForkIsLimit
  target_equalizer_universal := targetEqualizerForkIsLimit
""",
        """  source_equalizer_universal := fun S U =>
    ⟨sourceEqualizerForkIsLimit S U⟩
  target_equalizer_universal := fun S U =>
    ⟨targetEqualizerForkIsLimit S U⟩
""",
        "Mock2 construct proof-packaged equalizer witnesses",
    )
    text = replace_exact(
        text,
        "noncomputable def checklist_9_standalone_zeroProfile :",
        "theorem checklist_9_standalone_zeroProfile :",
        "Mock2 restore checklist 9 theorem",
    )

    # Keep the integrated conclusion bundle proof-valued.  Proposition 20's
    # concrete certificate contains categorical data, so retain its complete
    # content under Nonempty in the Prop certificate.
    text = replace_exact(
        text,
        """structure PaperElementaryConclusions
    (D : PaperElementaryInputData) (P : PaperElementaryModel D) : Type 2 where
""",
        """structure PaperElementaryConclusions
    (D : PaperElementaryInputData) (P : PaperElementaryModel D) : Prop where
""",
        "Mock2 restore elementary conclusions to Prop",
    )
    text = replace_exact(
        text,
        """  proposition20_certificate :
    Proposition20ActualQGaugeSpecialization.ActualProposition20Certificate
      Proposition20ActualQGaugeSpecialization.AdaptedGeometryCover.canonical
""",
        """  proposition20_certificate :
    Nonempty
      (Proposition20ActualQGaugeSpecialization.ActualProposition20Certificate
        Proposition20ActualQGaugeSpecialization.AdaptedGeometryCover.canonical)
""",
        "Mock2 proof-package Proposition 20 certificate",
    )
    text = replace_exact(
        text,
        "noncomputable def canonicalZeroBridgeModel_certificate (D : PaperElementaryInputData) :",
        "theorem canonicalZeroBridgeModel_certificate (D : PaperElementaryInputData) :",
        "Mock2 restore canonical bridge theorem",
    )
    text = replace_exact(
        text,
        """  proposition20_certificate :=
    Proposition20ActualQGaugeSpecialization.checklist_8_P1_unconditional
""",
        """  proposition20_certificate :=
    ⟨Proposition20ActualQGaugeSpecialization.checklist_8_P1_unconditional⟩
""",
        "Mock2 construct proof-packaged Proposition 20 certificate",
    )

    # The paper-map certificate has only proposition-valued fields once the
    # standalone certificate is proof-valued, so restore its original theorem
    # interface directly.
    text = replace_exact(
        text,
        """/-- Machine-checkable certificate for the required paper map. -/
structure Certificate : Type 1 where
""",
        """/-- Machine-checkable certificate for the required paper map. -/
structure Certificate : Prop where
""",
        "Mock2 restore PaperMap certificate to Prop",
    )
    text = replace_exact(
        text,
        "noncomputable def certificate : Certificate where",
        "theorem certificate : Certificate where",
        "Mock2 restore PaperMap certificate theorem",
    )

    # Likewise, keep the final static acceptance bundle as a theorem.  Its
    # only remaining data-valued field is the concrete Proposition 20
    # certificate, which is already represented by Nonempty above.
    text = replace_exact(
        text,
        "structure StaticAcceptanceCertificate (D : PaperElementaryInputData) : Type 2 where",
        "structure StaticAcceptanceCertificate (D : PaperElementaryInputData) : Prop where",
        "Mock2 restore static acceptance to Prop",
    )
    text = replace_exact(
        text,
        "noncomputable def staticAcceptance_certificate (D : PaperElementaryInputData) :",
        "theorem staticAcceptance_certificate (D : PaperElementaryInputData) :",
        "Mock2 restore static acceptance theorem",
    )
    text = replace_exact(
        text,
        """  proposition20_canonicalCover_zeroModel :=
    Proposition20ActualQGaugeSpecialization.checklist_8_P1_unconditional
""",
        """  proposition20_canonicalCover_zeroModel :=
    ⟨Proposition20ActualQGaugeSpecialization.checklist_8_P1_unconditional⟩
""",
        "Mock2 construct static Proposition 20 proof package",
    )

    M2.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
