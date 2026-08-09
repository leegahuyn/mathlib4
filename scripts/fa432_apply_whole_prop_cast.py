from __future__ import annotations
import hashlib,sys
from pathlib import Path
P=Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'); B='71dc36f16ebea92d537aa40a5d420443e4bcb93ccb76fea31efb40a6cb5c3aa0'; t=P.read_text(); h=hashlib.sha256(t.encode()).hexdigest()
if h!=B: raise SystemExit(f'unexpected baseline {h}')
old='''  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp'''
V={
'cast_congr': '''  simp only [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq]
  exact cast (by congr 1 <;> with_reducible_and_instances rfl) hcomp''',
'eqmp_congr': '''  simp only [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq]
  exact Eq.mp (by congr 1 <;> with_reducible_and_instances rfl) hcomp''',
'cast_congr_arg': '''  simp only [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq]
  exact cast (by
    apply congrArg (fun G : AddCommGroup ℂ =>
      @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℂ G
        instInnerProductSpaceRealComplex.toModule
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ _ _)
    with_reducible_and_instances rfl) hcomp''',
'simpa_cast': '''  simpa only [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using
    (cast (by congr 1 <;> with_reducible_and_instances rfl) hcomp)''',
'convert_zero': '''  convert hcomp using 0 <;>
    with_reducible_and_instances rfl''',
'exact_of_heq': '''  have hh : HEq hcomp (show
      HasDerivAt (actualEdgeAmbientParam e)
        (actualEdgeNativeVelocity e t) (t : Real) from by
          exact hcomp) := by
    with_reducible_and_instances rfl
  exact eq_of_heq hh''',
}
if len(sys.argv)!=2 or sys.argv[1] not in V: raise SystemExit('usage: '+'|'.join(V))
v=sys.argv[1]
if t.count(old)!=1: raise SystemExit(f'anchor {t.count(old)}')
t=t.replace(old,V[v]); P.write_text(t); print('variant='+v); print('input_sha256='+h); print('output_sha256='+hashlib.sha256(t.encode()).hexdigest()); print('line_count='+str(len(t.splitlines())))
