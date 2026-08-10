#!/usr/bin/env python3
from __future__ import annotations
import importlib.util, sys
from pathlib import Path
ROOT=Path.cwd()
spec=importlib.util.spec_from_file_location('fa463base',ROOT/'scripts/fa463_prepare_lower_pred.py')
if spec is None or spec.loader is None: raise RuntimeError('cannot load FA463 base')
mod=importlib.util.module_from_spec(spec); sys.modules[spec.name]=mod; spec.loader.exec_module(mod)
mod.PROOFS['lower_index_rw']=mod.COMMON_PREFIX+'''  have hIndex : -1 + n = n - 1 := by ring
  have hExponentNorm :
      euclideanGaugeExponent n = euclideanGaugeExponent (-1 + n) + 1 := by
    rw [hIndex]
    exact hExponent
  have hPowNorm :
      ((z.im ^ (1 + euclideanGaugeExponent (-1 + n)) : ℝ) : ℂ) =
        ((z.im ^ euclideanGaugeExponent n : ℝ) : ℂ) := by
    have he : 1 + euclideanGaugeExponent (-1 + n) = euclideanGaugeExponent n := by
      linarith
    rw [he]
'''+mod.COMMON_BODY+'''  rw [hPowNorm]
  ring'''
mod.PROOFS['lower_index_simp']=mod.COMMON_PREFIX+'''  have hIndex : -1 + n = n - 1 := by ring
  have he : 1 + euclideanGaugeExponent (-1 + n) = euclideanGaugeExponent n := by
    rw [hIndex, hExponent]
    ring
'''+mod.COMMON_BODY+'''  rw [he]
  ring'''
if __name__=='__main__': mod.main()
