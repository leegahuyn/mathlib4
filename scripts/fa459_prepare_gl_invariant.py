#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path.cwd()
spec = importlib.util.spec_from_file_location(
    "fa459_prepare_base", ROOT / "scripts/fa459_prepare_true_first_cluster.py"
)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA459 base preparer")
mod = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mod
spec.loader.exec_module(mod)

# Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean provides
# SMulInvariantMeasure for GL(2,R), not for SL(2,R).  The selected representative
# is already packaged as selectedCosetGL q, so use that exact action while
# leaving every theorem proposition unchanged.
mod.SELECTED_AE_BODY = """by
  change
    selectedCosetGL q • modularHalfOpenTile =ᵐ[hyperbolicMeasure]
      selectedCosetGL q • ModularGroup.fdo
  exact Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq
    (selectedCosetGL q)
    (measurePreserving_smul (selectedCosetGL q)⁻¹
      hyperbolicMeasure).quasiMeasurePreserving
    modularHalfOpenTile_ae_eq_fdo"""

mod.HSELECTED_NEW = """  have hSelectedTile : MeasurableSet
      (gammaTwoCosetRep q • modularHalfOpenTile) := by
    change MeasurableSet (selectedCosetGL q • modularHalfOpenTile)
    exact MeasurableSet.const_smul modularHalfOpenTile_measurable
      (selectedCosetGL q)"""

if __name__ == "__main__":
    mod.main()
