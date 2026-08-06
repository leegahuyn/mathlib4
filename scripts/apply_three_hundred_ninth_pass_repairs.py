from __future__ import annotations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / 'PrimalitySheafVerification' / 'Mock2_Advanced.lean'


def first_line(text: str) -> str:
    return text.splitlines()[0] if text.splitlines() else ''


def rep(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    n = text.count(old)
    print(f'{label}: expected={expected} actual={n} before={first_line(old)!r} after={first_line(new)!r}')
    if n != expected:
        raise RuntimeError(f'{label}: expected {expected}, found {n}')
    return text.replace(old, new)


def levels(xs: list[str]) -> str:
    return ', '.join(xs)


text = M2A.read_text(encoding='utf-8')

# Bind otherwise-phantom universes in proof-indexed ledgers.
text = rep(text,
"""theorem KernelEvidence.sound {P : Prop} {proof : P}
    (_ : KernelEvidence proof) : P :=
  proof

/-- Exact theorem-level evidence for all fifty strategy rows.""",
"""theorem KernelEvidence.sound {P : Prop} {proof : P}
    (_ : KernelEvidence proof) : P :=
  proof

universe uSection7LaxMilgram

/-- Exact theorem-level evidence for all fifty strategy rows.""",
'Section7 declare evidence universe')
text = rep(text,
"""        (@UnnumberedFormulaLedger.equations1_13_to_1_16_complexRealLaxMilgramOperator_proved)""",
"""        (@UnnumberedFormulaLedger.equations1_13_to_1_16_complexRealLaxMilgramOperator_proved.{uSection7LaxMilgram})""",
'Section7 bind Lax-Milgram evidence universe')

text = rep(text,
"""theorem KernelEvidence.sound {P : Prop} {proof : P}
    (_ : KernelEvidence proof) : P :=
  proof

/-- Exact theorem-level evidence for all fifty P0 rows.""",
"""theorem KernelEvidence.sound {P : Prop} {proof : P}
    (_ : KernelEvidence proof) : P :=
  proof

universe uP0Riesz

/-- Exact theorem-level evidence for all fifty P0 rows.""",
'P0 declare Riesz evidence universe')
text = rep(text,
"""      KernelEvidence (@p01_dualConvention_correctedAndProved)""",
"""      KernelEvidence (@p01_dualConvention_correctedAndProved.{uP0Riesz})""",
'P0 bind Riesz evidence universe')

# Definition 12's actual universal property is universe-relative: the sheaf
# carrier G and target carrier G' live in the same category universe. Preserve
# that polymorphism explicitly instead of leaving an unprovable independent
# universe metavariable.
text = rep(text,
"""  | .definition12 =>
      ∀ {X E F G : Type*} [TopologicalSpace X]
          [AddCommGroup E] [Module ℂ E]
          [AddCommGroup F] [Module ℂ F]
          [AddCommGroup G] [Module ℂ G]
          {L : LinearPresheaf X E} {M : LinearPresheaf X F}
          (S : QGaugeVariableSheaf X E F G L M)
          {G' : Type*} [AddCommGroup G'] [Module ℂ G']
          (T : LinearPresheaf X G') (hT : IsLinearSheaf T)
          (f : TensorPresheafMorphism L M T),
        ∃! g : LinearPresheafMorphism S.sheaf T,
          ∀ (U : TopologicalSpace.Opens X)
            (s : TensorPresheafSection L M U),
            g.app U (S.include.app U s) = f.app U s
""",
"""  | .definition12 =>
      ∀ {X E F : Type*} {G G' : Type uSheafG} [TopologicalSpace X]
          [AddCommGroup E] [Module ℂ E]
          [AddCommGroup F] [Module ℂ F]
          [AddCommGroup G] [Module ℂ G]
          {L : LinearPresheaf X E} {M : LinearPresheaf X F}
          (S : QGaugeVariableSheaf X E F G L M)
          [AddCommGroup G'] [Module ℂ G']
          (T : LinearPresheaf X G') (hT : IsLinearSheaf T)
          (f : TensorPresheafMorphism L M T),
        ∃! g : LinearPresheafMorphism S.sheaf T,
          ∀ (U : TopologicalSpace.Opens X)
            (s : TensorPresheafSection L M U),
            g.app U (S.include.app U s) = f.app U s
""",
'Section51 align Definition12 carrier universes')
text = rep(text,
'      exact QGaugeVariableSheaf.factor_existsUnique',
'      exact @QGaugeVariableSheaf.factor_existsUnique',
'Section51 explicit factor theorem')

# Prevent implicit-lambda elaboration from eagerly instantiating the corrected
# theorem aliases before the branch binders are introduced.
for old, new, label in [
    ('      exact ⟨lemma31_localPower_correctedAndProved,',
     '      exact ⟨@lemma31_localPower_correctedAndProved,',
     'Section52 explicit Lemma31 theorem'),
    ('      exact lemma32_proved', '      exact @lemma32_proved',
     'Section52 explicit Lemma32 theorem'),
    ('      exact lemma33_proved', '      exact @lemma33_proved',
     'Section52 explicit Lemma33 theorem'),
    ('      exact lemma61_covariance_proved', '      exact @lemma61_covariance_proved',
     'Section52 explicit Lemma61 theorem'),
]:
    text = rep(text, old, new, label)

# Restore the actual FlatQTransport API that pass 297 over-shortened.
text = rep(text,
"""  | .proposition14 =>
      ∀ {V Model : Type*}
        [AddCommGroup V] [Module ℂ V]
        [AddCommGroup Model] [Module ℂ Model]
        (L : QLocalSystem V Model)
        (D : RadialDerivation)
        (C : AlgebraicRadialConnection D Model)
        (A : CorrectedLemmas.CorrectedPropositions.FlatQTransport.DependentRadialConnection L D),
        A.TrivializationCompatible C →
          A = L.connectionOfTrivialization D C
""",
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
'Section53 restore FlatQTransport proposition14 API')

# Proposition 20 uses the same universe-relative cover index supported by the
# sheaf locality/gluing interface. Keep X and ι polymorphic at one named level.
text = rep(text,
"""  | .proposition20 =>
      ∀ {X E : Type*} [TopologicalSpace X]
        [AddCommGroup E] [Module ℂ E]
        {ι : Type*}
        (D : GaugeDescentSheaf X E)
        {U : TopologicalSpace.Opens X}
        (V : ι → TopologicalSpace.Opens X)
        (hVU : ∀ i, V i ≤ U),
        U ≤ ⨆ i, V i →
          Function.Bijective
            (CorrectedLemmas.CorrectedPropositions.GlobalEqualizer.restrictionToCompatibleGaugeFamily
              D V hVU)
""",
"""  | .proposition20 =>
      ∀ {X : Type uSheafX} {E : Type*} [TopologicalSpace X]
        [AddCommGroup E] [Module ℂ E]
        {ι : Type uSheafX}
        (D : GaugeDescentSheaf X E)
        {U : TopologicalSpace.Opens X}
        (V : ι → TopologicalSpace.Opens X)
        (hVU : ∀ i, V i ≤ U),
        U ≤ ⨆ i, V i →
          Function.Bijective
            (CorrectedLemmas.CorrectedPropositions.GlobalEqualizer.restrictionToCompatibleGaugeFamily
              D V hVU)
""",
'Section53 align Proposition20 cover universe')
text = rep(text,
'      exact proposition20_restrictionBijection_correctedAndProved',
'      exact @proposition20_restrictionBijection_correctedAndProved',
'Section53 explicit Proposition20 theorem')

# After tying the proposition20 index to X, Section53 ClaimEvidence has fourteen
# universe parameters in the order exposed by Lean's error report.
p1 = ['u53P1H'] + ['0'] * 13
p11 = ['0'] * 6 + ['u53P11H'] + ['0'] * 7
p12 = ['0'] * 14
p14 = ['0'] * 7 + ['u53P14V', 'u53P14Model'] + ['0'] * 5
p16 = ['0'] * 9 + ['u53P16X', 'u53P16Fiber'] + ['0'] * 3
p17 = ['0'] * 11 + ['u53P17R', 'u53P17V', '0']
p18 = ['0', 'u53P18R'] + ['0'] * 11 + ['u53P18V']
p19 = ['0', '0', 'u53P19OneForm', 'u53P19TwoForm'] + ['0'] * 10
p20 = ['0'] * 4 + ['u53P20X', 'u53P20E'] + ['0'] * 8
assert all(len(x) == 14 for x in [p1, p11, p12, p14, p16, p17, p18, p19, p20])

univ_decl = """universe u53P1H u53P11H u53P14V u53P14Model
  u53P16X u53P16Fiber u53P17R u53P17V u53P18R u53P18V
  u53P19OneForm u53P19TwoForm u53P20X u53P20E

"""
text = rep(text,
"""theorem proposition1_claimEvidence_proved : ClaimEvidence .proposition1 :=
  claimEvidence .proposition1
""",
univ_decl + f"""theorem proposition1_claimEvidence_proved :
    ClaimEvidence.{{{levels(p1)}}} .proposition1 :=
  claimEvidence.{{{levels(p1)}}} .proposition1
""",
'Section53 bind proposition1 alias universes')
for nm, lv in [
    ('proposition11', p11), ('proposition12', p12), ('proposition14', p14),
    ('proposition16', p16), ('proposition17', p17), ('proposition18', p18),
    ('proposition19', p19), ('proposition20', p20),
]:
    old = f"""theorem {nm}_claimEvidence_proved : ClaimEvidence .{nm} :=
  claimEvidence .{nm}
"""
    new = f"""theorem {nm}_claimEvidence_proved :
    ClaimEvidence.{{{levels(lv)}}} .{nm} :=
  claimEvidence.{{{levels(lv)}}} .{nm}
"""
    text = rep(text, old, new, f'Section53 bind {nm} alias universes')

# Definition12 now shares its two carrier universes, so Section51 contributes
# 31 universe parameters; Section52 contributes 4 and Section53 contributes 14.
g51 = [f'uGlobal51_{i}' for i in range(1, 32)]
g52 = [f'uGlobal52_{i}' for i in range(1, 5)]
g53 = [f'uGlobal53_{i}' for i in range(1, 15)]
gall = g51 + g52 + g53
assert len(gall) == 49
udecl = 'universe\n  ' + ' '.join(gall) + '\n\n'
old = """/-- The semantic evidence family for all 57 named rows.  This is stronger than
`exhaustive`: it delegates each row to its section's proof-producing statement
rather than merely checking a disposition tag. -/
def ClaimEvidence : Claim → Prop
  | .definition c => Section51Closure.ClaimEvidence c
  | .«lemma» c => Section52Closure.ClaimEvidence c
  | .proposition c => Section53Closure.ClaimEvidence c
  | .finalClaim c => Section54Closure.ClaimEvidence c

theorem claimEvidence (c : Claim) : ClaimEvidence c := by
  cases c with
  | definition c => exact Section51Closure.claimEvidence c
  | «lemma» c => exact Section52Closure.claimEvidence c
  | proposition c => exact Section53Closure.claimEvidence c
  | finalClaim c => exact Section54Closure.claimEvidence c
"""
new = f"""/-- The semantic evidence family for all 57 named rows.  This is stronger than
`exhaustive`: it delegates each row to its section's proof-producing statement
rather than merely checking a disposition tag. -/
{udecl}def ClaimEvidence : Claim → Prop
  | .definition c => Section51Closure.ClaimEvidence.{{{levels(g51)}}} c
  | .«lemma» c => Section52Closure.ClaimEvidence.{{{levels(g52)}}} c
  | .proposition c => Section53Closure.ClaimEvidence.{{{levels(g53)}}} c
  | .finalClaim c => Section54Closure.ClaimEvidence c

theorem claimEvidence (c : Claim) :
    ClaimEvidence.{{{levels(gall)}}} c := by
  cases c with
  | definition c => exact Section51Closure.claimEvidence.{{{levels(g51)}}} c
  | «lemma» c => exact Section52Closure.claimEvidence.{{{levels(g52)}}} c
  | proposition c => exact Section53Closure.claimEvidence.{{{levels(g53)}}} c
  | finalClaim c => exact Section54Closure.claimEvidence c
"""
text = rep(text, old, new, 'Global named evidence bind all section universes')

# Close the file-level `noncomputable section` before closing the namespace.
text = rep(text,
'\nend AxiomAudit\n\nend Mock2Adv\n',
'\nend AxiomAudit\n\nend\n\nend Mock2Adv\n',
'close final noncomputable section')

M2A.write_text(text, encoding='utf-8')
print('[pass309] Mock2_Advanced universe and evidence repairs applied')
