#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, importlib.util, json, sys
from pathlib import Path

ROOT = Path.cwd()
SRC = ROOT / 'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
BASE_SHA = '4647a9463e4264a7f0e08405b7ccd1ce9be87e7227fa2b91dc52024e2e198152'
LINES = 60453
TARGET = 'selectedHalfOpenTile_ae_eq_openTile'
spec = importlib.util.spec_from_file_location(
    'fa446base', ROOT / 'scripts/fa442_prepare_same_height_candidate.py')
if spec is None or spec.loader is None:
    raise RuntimeError('cannot load FA442 same-height utilities')
m = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = m
spec.loader.exec_module(m)


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def rep(text: str, old: str, new: str, label: str):
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'{label}: expected 1 found {count}')
    return text.replace(old, new), {'repair': label, 'applied': 1}


def in_decl(text: str, name: str, old: str, new: str, label: str) -> str:
    marker = f'theorem {name}'
    start = text.find(marker)
    if start < 0:
        raise RuntimeError(f'{label}: declaration missing')
    end = len(text)
    for token in ('\ntheorem ', '\nlemma ', '\nnoncomputable def ', '\ndef '):
        index = text.find(token, start + len(marker))
        if index >= 0:
            end = min(end, index + 1)
    block = text[start:end]
    count = block.count(old)
    if count != 1:
        raise RuntimeError(f'{label}: expected 1 found {count}')
    return text[:start] + block.replace(old, new) + text[end:]


def measurable(text: str):
    return rep(
        text,
        'open HalfWeightDifferentialOperators SmoothCompactCoreGeometry\n\n'
        '/-! #### A. The selected open and half-open tiles agree almost everywhere -/',
        'open HalfWeightDifferentialOperators SmoothCompactCoreGeometry\n'
        'local instance : MeasurableConstSMul SL(2, ℤ) ℍ := '
        '⟨fun g => (HalfIntegralMultiplier.continuous_sl2z_smul g).measurable⟩\n'
        '/-! #### A. The selected open and half-open tiles agree almost everywhere -/',
        'measurable_const_smul')


def height(text: str):
    return rep(
        text,
        '        (show z ∈ {w : ℍ | w.im ≤ H} from le_of_not_gt hHigh)⟩\n',
        '        (show z.im ≤ H from le_of_not_gt hHigh)⟩\n',
        'height_membership')


def upper(text: str):
    records = []
    text, record = rep(
        text, '    hcomplex.subtype_mk _\n',
        '    hcomplex.upperHalfPlaneMk _\n', 'upperHalfPlaneMk')
    records.append(record)
    text, record = rep(
        text,
        '      apply Subtype.ext\n      apply Complex.ext <;> simp)\n',
        '      apply UpperHalfPlane.ext\n      apply Complex.ext <;> simp)\n',
        'upperHalfPlane_ext')
    records.append(record)
    return text, {'repair': 'upper_cluster', 'details': records}


def pointwise(text: str):
    old = '''  change
    (selectedCuspTraceWeight n q Y t : ℂ) *
        (((u : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t)) +
         ((v : SmoothQuotientCompactFunction)
          (gammaTwoSelectedHorocycleParam q Y t))) = _
  ring
'''
    new = '''  change
    (selectedCuspTraceWeight n q Y t : ℂ) *
      (((u : SmoothQuotientCompactFunction) (gammaTwoSelectedHorocycleParam q Y t)) +
       ((v : SmoothQuotientCompactFunction) (gammaTwoSelectedHorocycleParam q Y t))) =
      (selectedCuspTraceWeight n q Y t : ℂ) * ((u : SmoothQuotientCompactFunction) (gammaTwoSelectedHorocycleParam q Y t)) +
      (selectedCuspTraceWeight n q Y t : ℂ) * ((v : SmoothQuotientCompactFunction) (gammaTwoSelectedHorocycleParam q Y t))
  exact mul_add _ _ _
'''
    return rep(text, old, new, 'pointwise_add')


def memspace(text: str):
    old = '''    MemLp (selectedCuspRestrictionRepresentative n q Y u) 2
      selectedHorocycleParameterMeasure := by
  let f := selectedCuspRestrictionRepresentative n q Y u
'''
    new = '''    MemLp (selectedCuspRestrictionRepresentative n q Y u) 2
      selectedHorocycleParameterMeasure := by
  letI : MeasurableSpace ℝ := Real.measureSpace.toMeasurableSpace
  let f := selectedCuspRestrictionRepresentative n q Y u
'''
    text, first = rep(text, old, new, 'measurable_space_alignment')
    old2 = '''  simpa only [Pi.pow_apply] using
    (hf.norm.pow 2).continuousOn.integrableOn_Icc

/-- The actual complex-linear smooth-core trace map. -/
'''
    new2 = '''  simpa only [Pi.pow_apply] using
    (hf.norm.pow 2).continuousOn.integrableOn_Icc
/-- The actual complex-linear smooth-core trace map. -/
'''
    text, second = rep(
        text, old2, new2, 'measurable_space_height_compensation')
    return text, {
        'repair': 'measurable_space_cluster',
        'details': [first, second],
    }


def lp(text: str):
    old = '''theorem coeFn_selectedCuspCoreTrace
    (n : ℤ) (q : GammaTwoRightCoset) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ⇑(selectedCuspCoreTrace n q Y u) =ᵐ[
      selectedHorocycleParameterMeasure]
        selectedCuspRestrictionRepresentative n q Y u := by
  simpa only [selectedCuspCoreTrace] using
    MemLp.coeFn_toLp
      (selectedCuspRestrictionRepresentative_memLp n q Y u)

'''
    new = '''theorem coeFn_selectedCuspCoreTrace
    (n : ℤ) (q : GammaTwoRightCoset) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ⇑(selectedCuspCoreTrace n q Y u) =ᵐ[
      selectedHorocycleParameterMeasure]
        selectedCuspRestrictionRepresentative n q Y u := by
  change ⇑((selectedCuspRestrictionRepresentative_memLp n q Y u).toLp
    (selectedCuspRestrictionRepresentative n q Y u)) =ᵐ[selectedHorocycleParameterMeasure]
      selectedCuspRestrictionRepresentative n q Y u
  exact MemLp.coeFn_toLp (selectedCuspRestrictionRepresentative_memLp n q Y u)
'''
    return rep(text, old, new, 'lp_representative')


def tail(text: str):
    old = '''  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u)
      .eventually_zero_on_horocycleBoundary with
'''
    new = '''  rcases (fixedPhaseCore_hasZeroThreeCuspTail n u).eventually_zero_on_horocycleBoundary with
'''
    count = text.count(old)
    if count != 2:
        raise RuntimeError(f'tail projection: expected 2 found {count}')
    text = text.replace(old, new)
    for name in (
        'fixedPhaseCore_eventually_selectedCuspRepresentative_ae_zero',
        'fixedPhaseCore_eventually_selectedCuspSection_eq_zero',
    ):
        text = in_decl(
            text, name,
            '  refine ⟨Y₀, hY₀, ?_⟩\n',
            '  refine ⟨Y₀, hY₀,\n    ?_⟩\n',
            f'{name}_height_compensation')
    return text, {
        'repair': 'tail_projection',
        'applied': 2,
        'height_compensation': 2,
    }


def zero(text: str):
    return rep(
        text,
        '  simpa using htrace.trans hrep\n',
        '  simpa only [Pi.zero_apply] using htrace.trans hrep\n',
        'zero_coercion')


OPS = [measurable, height, upper, pointwise, memspace, lp, tail, zero]
VARIANTS = {
    'baseline': 0,
    'measurable_only': 1,
    'measurable_height': 2,
    'measurable_height_upper': 3,
    'measurable_height_upper_pointwise': 4,
    'measurable_height_upper_pointwise_memspace': 5,
    'measurable_height_upper_pointwise_memspace_lp': 6,
    'measurable_height_upper_pointwise_memspace_lp_tail': 7,
    'measurable_height_upper_pointwise_memspace_lp_tail_zero': 8,
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--variant', required=True, choices=VARIANTS)
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    baseline = SRC.read_text(encoding='utf-8')
    actual = sha(baseline)
    if actual != BASE_SHA:
        raise RuntimeError(f'unexpected baseline SHA256: {actual}')
    if m.line_count(baseline) != LINES:
        raise RuntimeError('unexpected baseline line count')
    header = m.declaration_header(baseline, TARGET)
    header_sha = sha(header)
    candidate = baseline
    records = []
    for operation in OPS[:VARIANTS[args.variant]]:
        candidate, record = operation(candidate)
        records.append(record)
    if m.line_count(candidate) != LINES:
        raise RuntimeError(
            f'candidate height changed: {m.line_count(candidate)} != {LINES}')
    if m.declaration_header(candidate, TARGET) != header:
        raise RuntimeError('selectedHalfOpenTile theorem header changed')
    forbidden = m.forbidden_counts(candidate)
    if any(forbidden.values()):
        raise RuntimeError(f'forbidden-token audit failed: {forbidden}')
    SRC.write_text(candidate, encoding='utf-8')
    (output / 'Mock2_FunctionalAnalysis-baseline.lean').write_text(
        baseline, encoding='utf-8')
    (output / 'Mock2_FunctionalAnalysis-candidate.lean').write_text(
        candidate, encoding='utf-8')
    metadata = {
        'variant': args.variant,
        'baseline_sha256': BASE_SHA,
        'candidate_sha256': sha(candidate),
        'line_count': LINES,
        'same_height': True,
        'target_declaration': TARGET,
        'target_header_sha256': header_sha,
        'theorem_header_unchanged': True,
        'candidate_forbidden_counts': forbidden,
        'repairs': records,
    }
    (output / 'CANDIDATE.json').write_text(
        json.dumps(metadata, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(metadata, indent=2))


if __name__ == '__main__':
    main()
