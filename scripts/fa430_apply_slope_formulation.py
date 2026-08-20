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
old='''  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp'''
variants={
'slope_simpa': '''  rw [hasDerivAt_iff_tendsto_slope_zero] at hcomp ⊢
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
'slope_simpa_structures': '''  rw [hasDerivAt_iff_tendsto_slope_zero] at hcomp ⊢
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq,
    Complex.addCommGroup, Complex.instNormedAddCommGroup] using hcomp''',
'slope_dsimp': '''  rw [hasDerivAt_iff_tendsto_slope_zero] at hcomp ⊢
  dsimp [actualEdgeAmbientParam, actualEdgeNativeVelocity] at hcomp ⊢
  simpa [Function.comp_def, modularTileEdgeAmbientVelocity_eq] using hcomp''',
'slope_change_convert': '''  rw [hasDerivAt_iff_tendsto_slope_zero] at hcomp ⊢
  convert hcomp using 1 <;>
    simp [actualEdgeAmbientParam, actualEdgeNativeVelocity,
      Function.comp_def, modularTileEdgeAmbientVelocity_eq,
      Complex.addCommGroup, Complex.instNormedAddCommGroup]''',
'fderiv_unfold': '''  unfold HasDerivAt HasDerivAtFilter at hcomp ⊢
  simpa [actualEdgeAmbientParam, actualEdgeNativeVelocity,
    Function.comp_def, modularTileEdgeAmbientVelocity_eq,
    Complex.addCommGroup, Complex.instNormedAddCommGroup] using hcomp''',
'fderiv_convert': '''  unfold HasDerivAt HasDerivAtFilter at hcomp ⊢
  convert hcomp using 1 <;>
    simp [actualEdgeAmbientParam, actualEdgeNativeVelocity,
      Function.comp_def, modularTileEdgeAmbientVelocity_eq,
      Complex.addCommGroup, Complex.instNormedAddCommGroup]''',
}
if len(sys.argv)!=2 or sys.argv[1] not in variants:
    raise SystemExit('usage: fa430_apply_slope_formulation.py '+'|'.join(variants))
variant=sys.argv[1]
if text.count(old)!=1:
    raise SystemExit(f'anchor expected once, found {text.count(old)}')
text=text.replace(old,variants[variant])
TARGET.write_text(text,encoding='utf-8')
print('variant='+variant)
print('input_sha256='+actual)
print('output_sha256='+hashlib.sha256(text.encode()).hexdigest())
print('line_count='+str(len(text.splitlines())))
