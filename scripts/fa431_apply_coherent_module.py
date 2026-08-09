from __future__ import annotations
import hashlib,sys
from pathlib import Path
P=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
BASE='71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0'
t=P.read_text(); h=hashlib.sha256(t.encode()).hexdigest()
if h!=BASE: raise SystemExit(f'unexpected baseline {h}')
old='''  letI : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup
  letI : AddCommGroup Complex := Complex.addCommGroup'''
V={
'legacy_complex_module': '''  letI : AddCommGroup ℂ := Complex.addCommGroup
  letI : Module ℝ ℂ := Complex.instModule''',
'legacy_inner_module': '''  letI : AddCommGroup ℂ := Complex.addCommGroup
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule''',
'legacy_complex_module_normed': '''  letI : AddCommGroup ℂ := Complex.addCommGroup
  letI : Module ℝ ℂ := Complex.instModule
  letI : NormedSpace ℝ ℂ := NormedSpace.complexToReal''',
'legacy_inner_module_normed': '''  letI : AddCommGroup ℂ := Complex.addCommGroup
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  letI : NormedSpace ℝ ℂ := NormedSpace.complexToReal''',
'canonical_complex_module': '''  letI : AddCommGroup ℂ := Complex.instNormedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℂ := Complex.instModule''',
'legacy_module_then_group': '''  letI : Module ℝ ℂ := Complex.instModule
  letI : AddCommGroup ℂ := Complex.addCommGroup''',
}
if len(sys.argv)!=2 or sys.argv[1] not in V: raise SystemExit('usage: '+'|'.join(V))
v=sys.argv[1]
if t.count(old)!=1: raise SystemExit(f'anchor found {t.count(old)}')
t=t.replace(old,V[v]); P.write_text(t)
print('variant='+v); print('input_sha256='+h); print('output_sha256='+hashlib.sha256(t.encode()).hexdigest()); print('line_count='+str(len(t.splitlines())))
