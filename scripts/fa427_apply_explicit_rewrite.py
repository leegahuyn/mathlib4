from __future__ import annotations

import hashlib
import sys
from pathlib import Path

TARGET=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
BASE='71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0'
text=TARGET.read_text(encoding='utf-8')
actual=hashlib.sha256(text.encode()).hexdigest()
if actual != BASE:
    raise SystemExit(f'unexpected baseline {actual}')
if len(text.splitlines()) != 60453:
    raise SystemExit('unexpected baseline line count')

old='''  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp'''
canon='Complex.instNormedAddCommGroup.toAddCommGroup'
legacy='Complex.addCommGroup'

variants={
'legacy_at_hcomp_rfl': f'''  have hgroups : {canon} =
      {legacy} := by
    with_reducible_and_instances rfl
  rw [hgroups] at hcomp
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
'canonical_at_goal_rfl': f'''  have hgroups : {canon} =
      {legacy} := by
    with_reducible_and_instances rfl
  rw [← hgroups]
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
'legacy_at_hcomp_ext': f'''  have hgroups : {canon} =
      {legacy} := by
    ext <;> rfl
  rw [hgroups] at hcomp
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
'canonical_at_goal_ext': f'''  have hgroups : {canon} =
      {legacy} := by
    ext <;> rfl
  rw [← hgroups]
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
'simpa_with_group_eq': f'''  have hgroups : {canon} =
      {legacy} := by
    with_reducible_and_instances rfl
  simpa [hgroups, actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
'unfold_deriv_reducible': '''  with_reducible_and_instances
    simpa [HasDerivAt, HasDerivAtFilter, actualEdgeAmbientParam,
      actualEdgeNativeVelocity, Function.comp_def,
      modularTileEdgeAmbientVelocity_eq] using hcomp''',
}
if len(sys.argv) != 2 or sys.argv[1] not in variants:
    raise SystemExit('usage: fa427_apply_explicit_rewrite.py ' + '|'.join(variants))
variant=sys.argv[1]
if text.count(old) != 1:
    raise SystemExit(f'final proof anchor expected once, found {text.count(old)}')
text=text.replace(old,variants[variant])
TARGET.write_text(text,encoding='utf-8')
print('variant='+variant)
print('input_sha256='+actual)
print('output_sha256='+hashlib.sha256(text.encode()).hexdigest())
print('line_count='+str(len(text.splitlines())))
