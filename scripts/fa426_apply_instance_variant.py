from __future__ import annotations

import hashlib
import sys
from pathlib import Path

TARGET = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
BASELINE_SHA = '71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0'

text = TARGET.read_text(encoding='utf-8')
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != BASELINE_SHA:
    raise SystemExit(f'unexpected checked-in baseline: {actual}')
if len(text.splitlines()) != 60453:
    raise SystemExit(f'unexpected baseline line count: {len(text.splitlines())}')

old_simpa = '''  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp'''
old_legacy = '  letI : AddCommGroup Complex := Complex.addCommGroup'

variants = {
    'reducible_simpa': '''  with_reducible_and_instances
    simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
      Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
    'reducible_convert': '''  with_reducible_and_instances
    convert hcomp using 1 <;> simp [actualEdgeAmbientParam,
      actualEdgeNativeVelocity, Function.comp_def,
      modularTileEdgeAmbientVelocity_eq]''',
    'group_eq_reducible': '''  have hgroups : Complex.instNormedAddCommGroup.toAddCommGroup =
      Complex.addCommGroup := by
    with_reducible_and_instances rfl
  cases hgroups
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
    'group_eq_symm_reducible': '''  have hgroups : Complex.addCommGroup =
      Complex.instNormedAddCommGroup.toAddCommGroup := by
    with_reducible_and_instances rfl
  cases hgroups
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
    'unfold_instances': '''  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq,
    Complex.addCommGroup, Complex.instNormedAddCommGroup] using hcomp''',
    'canonical_only_reducible_simpa': '''  with_reducible_and_instances
    simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
      Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
}

if len(sys.argv) != 2 or sys.argv[1] not in variants:
    raise SystemExit('usage: fa426_apply_instance_variant.py ' + '|'.join(variants))
variant = sys.argv[1]
if text.count(old_simpa) != 1:
    raise SystemExit(f'expected current simpa once, found {text.count(old_simpa)}')
text = text.replace(old_simpa, variants[variant])
if variant == 'canonical_only_reducible_simpa':
    if text.count(old_legacy) != 1:
        raise SystemExit(f'expected legacy local instance once, found {text.count(old_legacy)}')
    text = text.replace(old_legacy, '  -- canonical additive structure only')

TARGET.write_text(text, encoding='utf-8')
print('variant=' + variant)
print('input_sha256=' + actual)
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('line_count=' + str(len(text.splitlines())))
