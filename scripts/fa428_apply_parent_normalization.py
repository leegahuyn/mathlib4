from __future__ import annotations

import hashlib
import sys
from pathlib import Path

TARGET=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
BASE='71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0'
text=TARGET.read_text(encoding='utf-8')
actual=hashlib.sha256(text.encode()).hexdigest()
if actual != BASE:
    raise SystemExit(f'unexpected baseline: {actual}')
if len(text.splitlines()) != 60453:
    raise SystemExit(f'unexpected baseline line count: {len(text.splitlines())}')

old='''  letI : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup
  letI : AddCommGroup Complex := Complex.addCommGroup'''

variants={
'custom_normed_group': '''  letI : NormedAddCommGroup ℂ :=
    { Complex.instNormedAddCommGroup with
      toAddCommGroup := Complex.addCommGroup }''',
'custom_normed_group_explicit_add': '''  letI : NormedAddCommGroup ℂ :=
    { Complex.instNormedAddCommGroup with
      toAddCommGroup := Complex.addCommGroup }
  letI : AddCommGroup ℂ := Complex.addCommGroup''',
'custom_normed_group_infer': '''  letI : NormedAddCommGroup ℂ :=
    { (inferInstance : NormedAddCommGroup ℂ) with
      toAddCommGroup := Complex.addCommGroup }''',
'custom_normed_field': '''  letI : NormedField ℂ :=
    { Complex.instNormedField with
      toAddCommGroup := Complex.addCommGroup }''',
'custom_normed_field_explicit_add': '''  letI : NormedField ℂ :=
    { Complex.instNormedField with
      toAddCommGroup := Complex.addCommGroup }
  letI : AddCommGroup ℂ := Complex.addCommGroup''',
'custom_normed_group_then_reducible': '''  letI : NormedAddCommGroup ℂ :=
    { Complex.instNormedAddCommGroup with
      toAddCommGroup := Complex.addCommGroup }
  letI : AddCommGroup ℂ :=
    (inferInstance : NormedAddCommGroup ℂ).toAddCommGroup''',
}

if len(sys.argv)!=2 or sys.argv[1] not in variants:
    raise SystemExit('usage: fa428_apply_parent_normalization.py '+'|'.join(variants))
variant=sys.argv[1]
if text.count(old)!=1:
    raise SystemExit(f'instance block expected once, found {text.count(old)}')
text=text.replace(old,variants[variant])
TARGET.write_text(text,encoding='utf-8')
print('variant='+variant)
print('input_sha256='+actual)
print('output_sha256='+hashlib.sha256(text.encode()).hexdigest())
print('line_count='+str(len(text.splitlines())))
