#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
META = ROOT / "build-logs" / "codex-fa496-graph-integral-shape" / "prepare.json"
PREV = ROOT / "scripts" / "fa495_prepare_orbit_l2_inner_field.py"

REQUIRED_FA495_RUN = 31464238170
REQUIRED_FA495_JOB = 93693691898
REQUIRED_FA495_HEAD = "a791a5deea1de804049c44cebbc6b5f04fde1032"
REQUIRED_FA495_SOURCE = "0cea98064a3970aa66099eec020fc787910584231a7dac68f5e27c71d5aa32bd"
REQUIRED_FA495_LINE = 35642
REQUIRED_FA495_COL = 6
REQUIRED_DECL_INDEX = 2821
REQUIRED_LINES = 60535
DECL = "integral_fixedPhaseEuclideanGraphDensity_eq_coordinates"

OLD = '''  rw [integral_add ((hBase.const_mul _).add (hRaise.const_mul _))
      (hLower.const_mul _),
    integral_add (hBase.const_mul _) (hRaise.const_mul _),
'''

NEW = '''  rw [integral_add (f := fun z => logHeightTraceBaseCoeff n * ‖fixedPhaseEuclideanGauge n u z‖ ^ 2 + 3 * ‖fixedPhaseEuclideanGauge (n + 1) (InverseEtaFixedPhaseCore.raise n u) z‖ ^ 2) (g := fun z => 3 * ‖fixedPhaseEuclideanGauge (n - 1) (InverseEtaFixedPhaseCore.lower n u) z‖ ^ 2) ((hBase.const_mul _).add (hRaise.const_mul _))
      (hLower.const_mul _),
    integral_add (f := fun z => logHeightTraceBaseCoeff n * ‖fixedPhaseEuclideanGauge n u z‖ ^ 2) (g := fun z => 3 * ‖fixedPhaseEuclideanGauge (n + 1) (InverseEtaFixedPhaseCore.raise n u) z‖ ^ 2) (hBase.const_mul _) (hRaise.const_mul _),
'''


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def load_prev():
    spec = importlib.util.spec_from_file_location("fa495_prepare", PREV)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load FA495 prepare")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def main() -> None:
    prev = load_prev()
    prev.main()
    text = SRC.read_text()
    before_sha = sha(text)
    if before_sha != REQUIRED_FA495_SOURCE:
        raise RuntimeError(f"FA495 source mismatch: {before_sha}")
    if len(text.splitlines()) != REQUIRED_LINES:
        raise RuntimeError("line-count drift before FA496")
    start = text.index(f"theorem {DECL}")
    next_decl = text.find("\ntheorem ", start + 1)
    region_end = len(text) if next_decl < 0 else next_decl
    region = text[start:region_end]
    if region.count(OLD) != 1:
        raise RuntimeError(f"expected one target fragment in {DECL}, got {region.count(OLD)}")
    replaced = region.replace(OLD, NEW, 1)
    out = text[:start] + replaced + text[region_end:]
    if len(out.splitlines()) != REQUIRED_LINES:
        raise RuntimeError(f"FA496 must preserve line count: {len(out.splitlines())}")
    SRC.write_text(out)
    after_sha = sha(out)
    meta = {
        "declaration": DECL,
        "declaration_index": REQUIRED_DECL_INDEX,
        "strategy": "pin integral_add implicit f/g to the exact pointwise lambda shapes while reusing the existing integrability witnesses",
        "matrix_variant": "named_pointwise_integrands",
        "required_fa495_evidence_run_id": REQUIRED_FA495_RUN,
        "required_fa495_evidence_job_id": REQUIRED_FA495_JOB,
        "required_fa495_evidence_head_sha": REQUIRED_FA495_HEAD,
        "required_fa495_source_sha256": REQUIRED_FA495_SOURCE,
        "required_fa495_first_error_line": REQUIRED_FA495_LINE,
        "required_fa495_first_error_col": REQUIRED_FA495_COL,
        "frontier_declaration_index": REQUIRED_DECL_INDEX,
        "later_repair_count": 0,
        "max_errors": 32,
        "fa495_intermediate_source_sha256": before_sha,
        "candidate_source_sha256": after_sha,
        "required_line_count": REQUIRED_LINES,
        "candidate_line_count": len(out.splitlines()),
        "replacement_count": 1,
        "old_fragment_sha256": sha(OLD),
        "new_fragment_sha256": sha(NEW),
    }
    META.parent.mkdir(parents=True, exist_ok=True)
    META.write_text(json.dumps(meta, indent=2) + "\n")
    print(json.dumps(meta, indent=2))


if __name__ == "__main__":
    main()
