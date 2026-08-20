from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def first_line(text: str) -> str:
    return text.splitlines()[0] if text.splitlines() else ""


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


def levels(names: list[str]) -> str:
    return ", ".join(names)


def main() -> int:
    text = M2A.read_text(encoding="utf-8")

    # The remaining Section-7 and P0 evidence rows each expose a genuinely
    # universe-polymorphic theorem.  Name those universes explicitly so the
    # finite evidence family has no unresolved level metavariables.
    text = replace_exact(
        text,
        "universe uSection7LaxMilgram",
        "universe uSection7LaxMilgram uSection7GapH uSection7GapHR uSection7GapHL",
        "Mock2 Advanced Section7 evidence universes",
    )
    text = replace_exact(
        text,
        "(@UnnumberedFormulaLedger.equations1_17_to_1_24_reducedPoincare_correctedAndProved)",
        "(@UnnumberedFormulaLedger.equations1_17_to_1_24_reducedPoincare_correctedAndProved.{uSection7GapH, uSection7GapHR, uSection7GapHL})",
        "Mock2 Advanced bind reduced-Poincare evidence universes",
    )
    text = replace_exact(
        text,
        "universe uP0Riesz",
        "universe uP0Riesz uP0StartX uP0StartT uP0StartV",
        "Mock2 Advanced P0 evidence universes",
    )
    text = replace_exact(
        text,
        "(@p02_distributionalRestriction_correctedAndProved)",
        "(@p02_distributionalRestriction_correctedAndProved.{uP0StartX, uP0StartT, uP0StartV})",
        "Mock2 Advanced bind starting-integral evidence universes",
    )

    # Preserve the universal-property statement while introducing its explicit
    # data in the order required by the current Mathlib declaration.
    text = replace_exact(
        text,
        "      exact @QGaugeVariableSheaf.factor_existsUnique",
        "      exact fun S T hT f => QGaugeVariableSheaf.factor_existsUnique S T hT f",
        "Mock2 Advanced Definition12 factor argument order",
    )

    # Parenthesize the intended Rankin--Selberg equivalence.  Without these
    # parentheses Lean parses the final iff outside the implication chain and
    # the evidence row no longer has the theorem's actual type.
    text = replace_exact(
        text,
        """  | .lemma31 =>
      (∀ {Y α σ : ℝ}, 0 < Y → 1 < σ →
        IntegrableOn
            (CorrectedLemmas.CuspConvergence.cuspPowerDensity
              (CorrectedLemmas.CuspConvergence.rankinSelbergGrowth α 1 σ))
            (Ioi Y) ↔
          α + σ < -(1 / 2 : ℝ)) ∧
        ¬ CorrectedLemmas.CuspConvergence.CitedLemma31RankinSelbergInference
""",
        """  | .lemma31 =>
      (∀ {Y α σ : ℝ}, 0 < Y → 1 < σ →
        (IntegrableOn
            (CorrectedLemmas.CuspConvergence.cuspPowerDensity
              (CorrectedLemmas.CuspConvergence.rankinSelbergGrowth α 1 σ))
            (Ioi Y) ↔
          α + σ < -(1 / 2 : ℝ))) ∧
        ¬ CorrectedLemmas.CuspConvergence.CitedLemma31RankinSelbergInference
""",
        "Mock2 Advanced Lemma31 implication-iff grouping",
    )

    # FlatQTransport defines the dependent connection in its namespace, while
    # QLocalSystem, RadialDerivation and AlgebraicRadialConnection are the
    # existing public root-level types.  Use those actual API paths.
    text = replace_exact(
        text,
        """  | .proposition14 =>
      ∀ {V Model : Type*}
        [AddCommGroup V] [Module ℂ V]
        [AddCommGroup Model] [Module ℂ Model]
        (L : CorrectedLemmas.CorrectedPropositions.FlatQTransport.QLocalSystem V Model)
        (D : CorrectedLemmas.CorrectedPropositions.FlatQTransport.RadialDerivation)
        (C : CorrectedLemmas.CorrectedPropositions.FlatQTransport.AlgebraicRadialConnection D Model)
        (A : CorrectedLemmas.CorrectedPropositions.FlatQTransport.DependentRadialConnection L D),
        A.TrivializationCompatible C →
          A = CorrectedLemmas.CorrectedPropositions.FlatQTransport.QLocalSystem.connectionOfTrivialization L D C
""",
        """  | .proposition14 =>
      ∀ {V Model : Type*}
        [AddCommGroup V] [Module ℂ V]
        [AddCommGroup Model] [Module ℂ Model]
        (L : QLocalSystem V Model)
        (D : RadialDerivation)
        (C : AlgebraicRadialConnection D Model)
        (A : CorrectedLemmas.CorrectedPropositions.FlatQTransport.DependentRadialConnection L D),
        A.TrivializationCompatible C →
          A = CorrectedLemmas.CorrectedPropositions.FlatQTransport.QLocalSystem.connectionOfTrivialization L D C
""",
        "Mock2 Advanced restore FlatQTransport public type paths",
    )

    # Give the concrete Section-5.3 witnesses as complete terms.  This avoids
    # placeholder metavariables being solved before the following tactic line,
    # which previously produced both a stuck CompleteSpace problem and several
    # spurious 'no goals' errors.
    text = replace_exact(
        text,
        """  | proposition1 =>
      simp only [ClaimEvidence]
      exact proposition1_closedBall_correctedAndProved
""",
        """  | proposition1 =>
      simp only [ClaimEvidence]
      exact fun f =>
        CorrectedLemmas.CorrectedPropositions.DualNorm.dualNorm_eq_sSup_closedUnitBall f
""",
        "Mock2 Advanced explicit Proposition1 evidence",
    )
    text = replace_exact(
        text,
        """  | proposition3 =>
      simp only [ClaimEvidence]
      refine ⟨1, by norm_num, ?_⟩
      exact
        CorrectedLemmas.CorrectedPropositions.AnalyticP2P7Completion.massConditionAt_smoothVolumeUnitData
          1 (by norm_num)
""",
        """  | proposition3 =>
      simp only [ClaimEvidence]
      exact ⟨1, by norm_num,
        CorrectedLemmas.CorrectedPropositions.AnalyticP2P7Completion.massConditionAt_smoothVolumeUnitData
          1 (by norm_num)⟩
""",
        "Mock2 Advanced closed Proposition3 witness",
    )
    text = replace_exact(
        text,
        """  | proposition4 =>
      simp only [ClaimEvidence]
      refine ⟨1, by norm_num, ?_⟩
      exact
        CorrectedLemmas.CorrectedPropositions.AnalyticP2P7Completion.hMass_smoothVolumeUnitData
          1 (by norm_num)
""",
        """  | proposition4 =>
      simp only [ClaimEvidence]
      exact ⟨1, by norm_num,
        CorrectedLemmas.CorrectedPropositions.AnalyticP2P7Completion.hMass_smoothVolumeUnitData
          1 (by norm_num)⟩
""",
        "Mock2 Advanced closed Proposition4 witness",
    )
    text = replace_exact(
        text,
        """  | proposition6 =>
      simp only [ClaimEvidence]
      refine ⟨1, by norm_num, ?_⟩
      intro m
      exact
        CorrectedLemmas.CorrectedPropositions.AnalyticP2P7Completion.massFunctional_smoothVolumeUnitData_pos
          1 (by norm_num) m
""",
        """  | proposition6 =>
      simp only [ClaimEvidence]
      exact ⟨1, by norm_num, fun m =>
        CorrectedLemmas.CorrectedPropositions.AnalyticP2P7Completion.massFunctional_smoothVolumeUnitData_pos
          1 (by norm_num) m⟩
""",
        "Mock2 Advanced closed Proposition6 witness",
    )
    text = replace_exact(
        text,
        """  | proposition7 =>
      simp only [ClaimEvidence]
      refine ⟨1, by norm_num, ?_⟩
      exact
        CorrectedLemmas.CorrectedPropositions.AnalyticP2P7Completion.hMass_smoothVolumeUnitData
          1 (by norm_num)
""",
        """  | proposition7 =>
      simp only [ClaimEvidence]
      exact ⟨1, by norm_num,
        CorrectedLemmas.CorrectedPropositions.AnalyticP2P7Completion.hMass_smoothVolumeUnitData
          1 (by norm_num)⟩
""",
        "Mock2 Advanced closed Proposition7 witness",
    )

    # Universe commands cannot be the declaration documented by a docstring.
    # Move the already verified 49-level binder before the public documentation.
    text = replace_exact(
        text,
        """/-- The semantic evidence family for all 57 named rows.  This is stronger than
`exhaustive`: it delegates each row to its section's proof-producing statement
rather than merely checking a disposition tag. -/
universe
  uGlobal51_1 uGlobal51_2 uGlobal51_3 uGlobal51_4 uGlobal51_5 uGlobal51_6 uGlobal51_7 uGlobal51_8 uGlobal51_9 uGlobal51_10 uGlobal51_11 uGlobal51_12 uGlobal51_13 uGlobal51_14 uGlobal51_15 uGlobal51_16 uGlobal51_17 uGlobal51_18 uGlobal51_19 uGlobal51_20 uGlobal51_21 uGlobal51_22 uGlobal51_23 uGlobal51_24 uGlobal51_25 uGlobal51_26 uGlobal51_27 uGlobal51_28 uGlobal51_29 uGlobal51_30 uGlobal51_31 uGlobal52_1 uGlobal52_2 uGlobal52_3 uGlobal52_4 uGlobal53_1 uGlobal53_2 uGlobal53_3 uGlobal53_4 uGlobal53_5 uGlobal53_6 uGlobal53_7 uGlobal53_8 uGlobal53_9 uGlobal53_10 uGlobal53_11 uGlobal53_12 uGlobal53_13 uGlobal53_14

def ClaimEvidence : Claim → Prop
""",
        """universe
  uGlobal51_1 uGlobal51_2 uGlobal51_3 uGlobal51_4 uGlobal51_5 uGlobal51_6 uGlobal51_7 uGlobal51_8 uGlobal51_9 uGlobal51_10 uGlobal51_11 uGlobal51_12 uGlobal51_13 uGlobal51_14 uGlobal51_15 uGlobal51_16 uGlobal51_17 uGlobal51_18 uGlobal51_19 uGlobal51_20 uGlobal51_21 uGlobal51_22 uGlobal51_23 uGlobal51_24 uGlobal51_25 uGlobal51_26 uGlobal51_27 uGlobal51_28 uGlobal51_29 uGlobal51_30 uGlobal51_31 uGlobal52_1 uGlobal52_2 uGlobal52_3 uGlobal52_4 uGlobal53_1 uGlobal53_2 uGlobal53_3 uGlobal53_4 uGlobal53_5 uGlobal53_6 uGlobal53_7 uGlobal53_8 uGlobal53_9 uGlobal53_10 uGlobal53_11 uGlobal53_12 uGlobal53_13 uGlobal53_14

/-- The semantic evidence family for all 57 named rows.  This is stronger than
`exhaustive`: it delegates each row to its section's proof-producing statement
rather than merely checking a disposition tag. -/
def ClaimEvidence : Claim → Prop
""",
        "Mock2 Advanced move global evidence universe binder",
    )

    # The combined checklist consumes all 49 global-claim levels plus four
    # Section-7 and four P0 levels.  Propagate them explicitly rather than
    # leaving a second layer of unresolved universe metavariables.
    global_levels = [f"uChecklistGlobal_{i}" for i in range(1, 50)]
    section7_levels = [f"uChecklistSection7_{i}" for i in range(1, 5)]
    p0_levels = [f"uChecklistP0_{i}" for i in range(1, 5)]
    all_levels = global_levels + section7_levels + p0_levels
    universe_decl = "universe\n  " + " ".join(all_levels) + "\n\n"

    old_checklist = """/-- Semantic evidence for every one of the 174 checklist rows.  Unlike
`IsTerminal`, this family delegates to the proof-producing statement selected
by the corresponding ledger. -/
def Evidence : Item → Prop
  | Sum.inl c => GlobalNamedClaimClosure.ClaimEvidence c
  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence c
  | Sum.inr (Sum.inr (Sum.inl r)) =>
      Section7WorkaroundLedger.RequirementEvidence r
  | Sum.inr (Sum.inr (Sum.inr r)) => P0RepairLedger.RequirementEvidence r

theorem evidence (i : Item) : Evidence i := by
  rcases i with c | c
  · exact GlobalNamedClaimClosure.claimEvidence c
  · rcases c with c | r
    · exact UnnumberedFormulaLedger.claimEvidence c
    · rcases r with r | r
      · exact Section7WorkaroundLedger.requirementEvidence r
      · exact P0RepairLedger.requirementEvidence r
"""
    new_checklist = f"""{universe_decl}/-- Semantic evidence for every one of the 174 checklist rows.  Unlike
`IsTerminal`, this family delegates to the proof-producing statement selected
by the corresponding ledger. -/
def Evidence : Item → Prop
  | Sum.inl c => GlobalNamedClaimClosure.ClaimEvidence.{{{levels(global_levels)}}} c
  | Sum.inr (Sum.inl c) => UnnumberedFormulaLedger.ClaimEvidence c
  | Sum.inr (Sum.inr (Sum.inl r)) =>
      Section7WorkaroundLedger.RequirementEvidence.{{{levels(section7_levels)}}} r
  | Sum.inr (Sum.inr (Sum.inr r)) =>
      P0RepairLedger.RequirementEvidence.{{{levels(p0_levels)}}} r

theorem evidence (i : Item) :
    Evidence.{{{levels(all_levels)}}} i := by
  rcases i with c | c
  · exact GlobalNamedClaimClosure.claimEvidence.{{{levels(global_levels)}}} c
  · rcases c with c | r
    · exact UnnumberedFormulaLedger.claimEvidence c
    · rcases r with r | r
      · exact Section7WorkaroundLedger.requirementEvidence.{{{levels(section7_levels)}}} r
      · exact P0RepairLedger.requirementEvidence.{{{levels(p0_levels)}}} r
"""
    text = replace_exact(
        text,
        old_checklist,
        new_checklist,
        "Mock2 Advanced propagate global checklist universes",
    )

    M2A.write_text(text, encoding="utf-8")
    print("[pass310] Mock2_Advanced evidence and universe frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
