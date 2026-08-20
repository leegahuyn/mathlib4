from __future__ import annotations

from pathlib import Path
import re
import textwrap

import apply_sixty_second_pass_repairs as pass62

ROOT = Path('PrimalitySheafVerification')


def replace_exact(text: str, old: str, new: str, expected: int, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == expected:
        print(f'{label}: applied {count}')
        return text.replace(old, new), True
    if count == 0 and new in text:
        print(f'{label}: already applied')
        return text, False
    if count == 0:
        print(f'{label}: source changed; skipped')
        return text, False
    raise RuntimeError(f'{label}: expected {expected} match(es), found {count}')


def _parse_list_entries(text: str, marker: str) -> list[str]:
    start = text.index(marker)
    start = text.index('[', start)
    end = text.index(']', start)
    block = text[start + 1:end]
    return re.findall(r'(?:^|,)\s*([A-Za-z][A-Za-z0-9_]*)', block, flags=re.M)


def _parse_leaf_ledger_fields(text: str) -> list[tuple[str, str]]:
    start = text.index('structure AdvancedClaimsIIRequirementLeafLedger')
    body_start = text.index('\n', start) + 1
    end = text.index('\nnamespace AdvancedClaimsIIRequirementLeafLedger', body_start)
    lines = text[body_start:end].splitlines()
    starts: list[tuple[int, str, str]] = []
    for i, line in enumerate(lines):
        m = re.match(r'^  ([A-Za-z][A-Za-z0-9_]*)\s*:\s*(.*)$', line)
        if m:
            starts.append((i, m.group(1), m.group(2)))
    fields: list[tuple[str, str]] = []
    for pos, (i, name, first) in enumerate(starts):
        j = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
        type_lines = []
        if first:
            type_lines.append(first)
        type_lines.extend(lines[i + 1:j])
        typ = textwrap.dedent('\n'.join(type_lines)).strip()
        fields.append((name, typ))
    return fields


def _leaf_statement_definition(text: str) -> str:
    constructors = _parse_list_entries(text, 'def all : List AdvancedClaimsIIRequirement :=')
    fields = _parse_leaf_ledger_fields(text)
    if len(constructors) != len(fields):
        raise RuntimeError(f'leaf statement shape mismatch: {len(constructors)} constructors, {len(fields)} fields')
    lines = [
        'def leafStatement',
        '    (C : AdvancedClaimsIICompletionCertificate) :',
        '    AdvancedClaimsIIRequirement → Prop',
    ]
    for ctor, (_field, typ) in zip(constructors, fields):
        tlines = typ.splitlines()
        lines.append(f'  | {ctor} =>')
        lines.extend('      ' + line for line in tlines)
    return '\n'.join(lines)


def _explicit_mem_all(text: str) -> str:
    entries = _parse_list_entries(text, 'def all : List AdvancedClaimsIIPromptBullet :=')
    lines = [
        'theorem mem_all',
        '    (b : AdvancedClaimsIIPromptBullet) :',
        '    List.Mem b all := by',
        '  cases b',
    ]
    for idx in range(len(entries)):
        term = 'List.Mem.head _'
        for _ in range(idx):
            term = f'List.Mem.tail _ ({term})'
        lines.append(f'  · exact {term}')
    return '\n'.join(lines)


def repair_mock1_advanced() -> None:
    path = ROOT / 'Mock1_Advanced.lean'
    text = path.read_text(encoding='utf-8')
    changed = False

    old = '''theorem mem_all
    (b : AdvancedClaimsIIPromptBullet) :
    List.Mem b all := by
  cases b <;> decide
'''
    new = _explicit_mem_all(text) + '\n'
    text, did = replace_exact(text, old, new, 1,
        'Mock1Advanced prove every prompt-bullet membership structurally')
    changed |= did

    leaf_def = _leaf_statement_definition(text)
    marker = '\nstructure AdvancedClaimsIIRequirementDispatchCertificate'
    if 'def leafStatement\n    (C : AdvancedClaimsIICompletionCertificate)' not in text:
        if marker not in text:
            raise RuntimeError('Mock1Advanced leafStatement insertion marker missing')
        text = text.replace(marker,
            '\nnamespace AdvancedClaimsIIRequirement\n\n' + leaf_def +
            '\n\nend AdvancedClaimsIIRequirement\n\nstructure AdvancedClaimsIIRequirementDispatchCertificate', 1)
        changed = True
        print('Mock1Advanced define all 54 requirement leaf statements from the ledger: applied')
    else:
        print('Mock1Advanced define all 54 requirement leaf statements from the ledger: already applied')

    statement_def = '''def statement
    (C : AdvancedClaimsIICompletionCertificate)
    (b : AdvancedClaimsIIPromptBullet) : Prop :=
  AdvancedClaimsIIRequirement.leafStatement C (requirementOf b)
'''
    marker2 = '\ntheorem requirement_mem_all\n'
    if 'def statement\n    (C : AdvancedClaimsIICompletionCertificate)' not in text:
        if marker2 not in text:
            raise RuntimeError('Mock1Advanced prompt statement insertion marker missing')
        text = text.replace(marker2, '\n' + statement_def + marker2, 1)
        changed = True
        print('Mock1Advanced define prompt statements through requirementOf: applied')
    else:
        print('Mock1Advanced define prompt statements through requirementOf: already applied')

    if changed:
        path.write_text(text, encoding='utf-8', newline='\n')


def repair_mock2() -> None:
    path = ROOT / 'Mock2.lean'
    text = path.read_text(encoding='utf-8')
    changed = False
    reps = [
        ('''            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ac_rfl
''','''            simp only [Nat.cast_mul, Nat.cast_pow, Int.cast_mul, Int.cast_natCast]
            ac_rfl
''',1,'Mock2 normalize both natural powers before factor reordering'),
        ('''  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    simpa [integerMul_apply] using hz
''','''  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    exact hz.trans (map_zero (integerMul M)).symm
''',1,'Mock2 compare multiplication with the mapped zero explicitly'),
        ('''@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  change freeResolutionD M (n + 2) = 0
  rfl
''','''@[simp] theorem freeResolutionComplex_d_succ_two_succ (M n : ℕ) :
    (freeResolutionComplex M).d (n + 3) (n + 2) = 0 := by
  change ChainComplex.of.d freeResolutionX (freeResolutionD M) (n + 3) (n + 2) = 0
  rw [ChainComplex.of_d]
  rfl
''',1,'Mock2 expose the higher differential through ChainComplex.of_d'),
        ('''  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  simpa [resolutionAtOne] using resolutionAtOne_exact M hM
''','''  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  convert resolutionAtOne_exact M hM using 1 <;> rfl
''',1,'Mock2 identify the degree-one short complex up to proof irrelevance'),
        ('''  exact (tensorRightFunctor N).map_isZero
    (CategoryTheory.Limits.isZero_zero :
      CategoryTheory.Limits.IsZero zeroIntegerModule)
''','''  exact (tensorRightFunctor N).map_isZero
    (ModuleCat.isZero_of_subsingleton zeroIntegerModule)
''',1,'Mock2 use the concrete zero module after tensoring'),
    ]
    for old,new,n,label in reps:
        text,did=replace_exact(text,old,new,n,label); changed|=did
    if changed: path.write_text(text,encoding='utf-8',newline='\n')


def repair_mock2_advanced() -> None:
    path = ROOT / 'Mock2_Advanced.lean'
    text = path.read_text(encoding='utf-8')
    changed = False
    marker='namespace Mock2Adv\n\nnoncomputable section'
    newmarker='namespace Mock2Adv\n\nuniverse uSheafX uSheafE uSheafF uSheafG\n\nnoncomputable section'
    text,did=replace_exact(text,marker,newmarker,1,'Mock2Advanced name fixed ambient sheaf universes'); changed|=did
    reps=[
      ('{X E : Type*} [TopologicalSpace X]\n    [AddCommGroup E] [Module ℂ E]\n    (P : LinearPresheaf X E) : Prop where\n  locality : ∀ {ι : Type*}',
       '{X : Type uSheafX} {E : Type uSheafE} [TopologicalSpace X]\n    [AddCommGroup E] [Module ℂ E]\n    (P : LinearPresheaf X E) : Prop where\n  locality : ∀ {ι : Type uSheafX}',1,'Mock2Advanced fix the locality cover universe'),
      ('  gluing : ∀ {ι : Type*} {U : TopologicalSpace.Opens X}',
       '  gluing : ∀ {ι : Type uSheafX} {U : TopologicalSpace.Opens X}',2,'Mock2Advanced fix linear and balanced gluing universes'),
      ('structure QGaugeVariableSheaf\n    (X E F G : Type*)',
       'structure QGaugeVariableSheaf\n    (X : Type uSheafX) (E : Type uSheafE)\n    (F : Type uSheafF) (G : Type uSheafG)',1,'Mock2Advanced name QGauge ambient universes'),
      ('  factor : ∀ {G\' : Type*}', '  factor : ∀ {G\' : Type uSheafG}',1,'Mock2Advanced fix factor target universe'),
      ('  factor_include : ∀ {G\' : Type*}', '  factor_include : ∀ {G\' : Type uSheafG}',1,'Mock2Advanced fix factor_include target universe'),
      ('  factor_unique : ∀ {G\' : Type*}', '  factor_unique : ∀ {G\' : Type uSheafG}',1,'Mock2Advanced fix factor_unique target universe'),
      ('theorem QGaugeVariableSheaf.factor_existsUnique\n    {X E F G : Type*} [TopologicalSpace X]',
       'theorem QGaugeVariableSheaf.factor_existsUnique\n    {X : Type uSheafX} {E : Type uSheafE}\n    {F : Type uSheafF} {G : Type uSheafG} [TopologicalSpace X]',1,'Mock2Advanced fix factor_existsUnique ambient universes'),
      ('    {X E F : Type*} [TopologicalSpace X]\n    [AddCommGroup E] [Module ℂ E]\n    [AddCommGroup F] [Module ℂ F]\n    {P : LinearPresheaf X E} {Q : LinearPresheaf X F}\n    (resIn resOut : LinearPresheafMorphism P Q)\n    (hP : IsLinearSheaf P)\n    {ι : Type*}',
       '    {X : Type uSheafX} {E : Type uSheafE} {F : Type uSheafF}\n    [TopologicalSpace X]\n    [AddCommGroup E] [Module ℂ E]\n    [AddCommGroup F] [Module ℂ F]\n    {P : LinearPresheaf X E} {Q : LinearPresheaf X F}\n    (resIn resOut : LinearPresheafMorphism P Q)\n    (hP : IsLinearSheaf P)\n    {ι : Type uSheafX}',1,'Mock2Advanced fix balanced locality theorem universes'),
      ('    {X E F : Type*} [TopologicalSpace X]\n    [AddCommGroup E] [Module ℂ E]\n    [AddCommGroup F] [Module ℂ F]\n    {P : LinearPresheaf X E} {Q : LinearPresheaf X F}\n    (resIn resOut : LinearPresheafMorphism P Q)\n    (hP : IsLinearSheaf P) (hQ : IsLinearSheaf Q)\n    {ι : Type*}',
       '    {X : Type uSheafX} {E : Type uSheafE} {F : Type uSheafF}\n    [TopologicalSpace X]\n    [AddCommGroup E] [Module ℂ E]\n    [AddCommGroup F] [Module ℂ F]\n    {P : LinearPresheaf X E} {Q : LinearPresheaf X F}\n    (resIn resOut : LinearPresheafMorphism P Q)\n    (hP : IsLinearSheaf P) (hQ : IsLinearSheaf Q)\n    {ι : Type uSheafX}',2,'Mock2Advanced fix balanced gluing theorem universes'),
      ('structure IsBalancedPresheafSheaf\n    {X E F : Type*}',
       'structure IsBalancedPresheafSheaf\n    {X : Type uSheafX} {E : Type uSheafE} {F : Type uSheafF}',1,'Mock2Advanced name balanced sheaf universes'),
      ('  locality : ∀ {ι : Type*}', '  locality : ∀ {ι : Type uSheafX}',1,'Mock2Advanced fix balanced locality field universe'),
      ('structure GaugeDescentSheaf\n    (X E : Type*)',
       'structure GaugeDescentSheaf\n    (X : Type uSheafX) (E : Type uSheafE)',1,'Mock2Advanced name gauge descent sheaf universes'),
      ('    {X E : Type*} [TopologicalSpace X]\n    [AddCommGroup E] [Module ℂ E]\n    (D : GaugeDescentSheaf X E)\n    {ι : Type*}',
       '    {X : Type uSheafX} {E : Type uSheafE} [TopologicalSpace X]\n    [AddCommGroup E] [Module ℂ E]\n    (D : GaugeDescentSheaf X E)\n    {ι : Type uSheafX}',2,'Mock2Advanced fix gauge gluing theorem universes'),
      ('variable {X Fiber : Type*} [TopologicalSpace X]',
       'variable {X : Type uSheafX} {Fiber : Type uSheafE} [TopologicalSpace X]',1,'Mock2Advanced name trivial bundle universes'),
      ('    {ι : Type*} {U : TopologicalSpace.Opens X}\n    (V : ι → TopologicalSpace.Opens X)',
       '    {ι : Type uSheafX} {U : TopologicalSpace.Opens X}\n    (V : ι → TopologicalSpace.Opens X)',1,'Mock2Advanced fix concrete gluing cover universe'),
    ]
    for old,new,n,label in reps:
      text,did=replace_exact(text,old,new,n,label); changed|=did

    theorem_pos = text.index('theorem QGaugeVariableSheaf.factor_existsUnique')
    target_old = "    {G' : Type*} [AddCommGroup G'] [Module ℂ G']"
    target_new = "    {G' : Type uSheafG} [AddCommGroup G'] [Module ℂ G']"
    target_pos = text.find(target_old, theorem_pos)
    if target_pos >= 0:
        text = text[:target_pos] + target_new + text[target_pos + len(target_old):]
        changed = True
        print('Mock2Advanced fix factor_existsUnique target universe: applied')
    elif target_new in text[theorem_pos:theorem_pos + 1000]:
        print('Mock2Advanced fix factor_existsUnique target universe: already applied')
    else:
        raise RuntimeError('Mock2Advanced factor_existsUnique target universe marker missing')

    if changed: path.write_text(text,encoding='utf-8',newline='\n')


def repair_functional_analysis() -> None:
    path=ROOT/'Mock2_FunctionalAnalysis.lean'; text=path.read_text(encoding='utf-8'); changed=False
    reps=[
      ('    simpa only [ModularForm.discriminant] using hΔ\n','    exact hΔ\n',1,'FunctionalAnalysis keep the discriminant equality without proof-sensitive simplification'),
      ('''  rw [inverseEtaRawFactor_eq, inverseEtaRawFactor_eq,
    inverseEtaRawFactor_eq, mul_smul]
  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
''','''  rw [inverseEtaRawFactor_eq, inverseEtaRawFactor_eq,
    inverseEtaRawFactor_eq, mul_smul]
  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  <;> ring
''',1,'FunctionalAnalysis restore denominator clearing in the eta cocycle'),
      ('    simpa only [inverseEtaRawFactor_zpow, map_mul] using h\n','''    change
      ((etaPhase (((γ * δ : Γ) : SL(2, ℤ))))⁻¹) ^ k *
          etaSqrtFactor (((γ * δ : Γ) : SL(2, ℤ))) z ^ (-k) = _
    rw [show (((γ * δ : Γ) : SL(2, ℤ))) =
      (γ : SL(2, ℤ)) * (δ : SL(2, ℤ)) by rfl]
    simpa only [inverseEtaRawFactor_zpow] using h
''',1,'FunctionalAnalysis identify the subgroup product before using the eta cocycle'),
      ('  carrier := {u | ∀ γ z,\n    u ((γ : SL(2, ℤ)) • z) = M.factor γ z * u z}\n',
       '  carrier := {u | ∀ (γ : Γ) z,\n    u ((γ : SL(2, ℤ)) • z) = M.factor γ z * u z}\n',1,'FunctionalAnalysis bind covariance to the actual subgroup'),
    ]
    for old,new,n,label in reps:
      text,did=replace_exact(text,old,new,n,label); changed|=did
    if changed: path.write_text(text,encoding='utf-8',newline='\n')


def main() -> int:
    pass62.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0

if __name__=='__main__': raise SystemExit(main())
