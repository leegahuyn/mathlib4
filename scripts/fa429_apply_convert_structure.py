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

old_final='''  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp'''
old_body='''  letI : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup
  letI : AddCommGroup Complex := Complex.addCommGroup
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
  have houter :=
    (selectedCosetAmbientMap_hasStrictFDerivAt e.1
      (modularTileEdgeParam e.2 t)).hasFDerivAt
  have hcomp := houter.comp_hasDerivAt_of_eq (t : Real) hbase
    (modularTileEdgeAmbientParam_eq_coe e.2 t).symm
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp'''

hgroup='''  have hgroups : Complex.instNormedAddCommGroup.toAddCommGroup =
      Complex.addCommGroup := by
    with_reducible_and_instances rfl'''
convert_prefix='''  convert hcomp using 1 <;> try simp [actualEdgeAmbientParam,
    actualEdgeNativeVelocity, Function.comp_def,
    modularTileEdgeAmbientVelocity_eq]'''

variants={
'convert_exact_hgroups': hgroup+'\n'+convert_prefix+'''\n  exact hgroups''',
'convert_exact_hgroups_symm': hgroup+'\n'+convert_prefix+'''\n  exact hgroups.symm''',
'convert_subsingleton': convert_prefix+'''\n  exact Subsingleton.elim _ _''',
'convert_cases_hgroups': hgroup+'''\n  cases hgroups\n'''+convert_prefix+'''\n  rfl''',
'cases_before_hcomp': '''  have hgroups : Complex.instNormedAddCommGroup.toAddCommGroup =
      Complex.addCommGroup := by
    with_reducible_and_instances rfl
  cases hgroups
  letI : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup
  letI : AddCommGroup Complex := Complex.addCommGroup
  have hbase := modularTileEdgeAmbientParam_hasDerivAt e.2 t
  have houter :=
    (selectedCosetAmbientMap_hasStrictFDerivAt e.1
      (modularTileEdgeParam e.2 t)).hasFDerivAt
  have hcomp := houter.comp_hasDerivAt_of_eq (t : Real) hbase
    (modularTileEdgeAmbientParam_eq_coe e.2 t).symm
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
'convert_trace_goal': convert_prefix+'''\n  trace_state\n  exact hcomp''',
}

if len(sys.argv)!=2 or sys.argv[1] not in variants:
    raise SystemExit('usage: fa429_apply_convert_structure.py '+'|'.join(variants))
variant=sys.argv[1]
if variant=='cases_before_hcomp':
    if text.count(old_body)!=1:
        raise SystemExit(f'body anchor expected once, found {text.count(old_body)}')
    text=text.replace(old_body,variants[variant])
else:
    if text.count(old_final)!=1:
        raise SystemExit(f'final anchor expected once, found {text.count(old_final)}')
    text=text.replace(old_final,variants[variant])
TARGET.write_text(text,encoding='utf-8')
print('variant='+variant)
print('input_sha256='+actual)
print('output_sha256='+hashlib.sha256(text.encode()).hexdigest())
print('line_count='+str(len(text.splitlines())))
