#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = ROOT / "scripts/fa442_prepare_same_height_candidate.py"

spec = importlib.util.spec_from_file_location("fa443_prepare_base", ORIGINAL)
if spec is None or spec.loader is None:
    raise RuntimeError(f"cannot load {ORIGINAL}")
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)


def apply_upper_half_plane_contextual(text: str):
    """Apply the two UpperHalfPlane API adaptations at their exact proof context.

    FA442 replaced the generic line ``apply Subtype.ext`` and therefore found
    four matches.  The constructor line and the following two-line extensionality
    block uniquely identify the intended declaration while preserving file
    height and every theorem header.
    """
    records: list[dict] = []
    text, count = module.replace_exact(
        text,
        "    hcomplex.subtype_mk _\n",
        "    hcomplex.upperHalfPlaneMk _\n",
    )
    records.append({"repair": "upperHalfPlaneMk", "applied": count})
    text, count = module.replace_exact(
        text,
        "      apply Subtype.ext\n      apply Complex.ext <;> simp)\n",
        "      apply UpperHalfPlane.ext\n      apply Complex.ext <;> simp)\n",
    )
    records.append({"repair": "UpperHalfPlane.ext_contextual", "applied": count})
    if module.line_count(text) != module.OUT_LINES:
        raise RuntimeError("contextual UpperHalfPlane repair changed file height")
    return text, {"repair": "upper_half_plane_cluster_contextual", "details": records}


module.apply_upper_half_plane = apply_upper_half_plane_contextual

if __name__ == "__main__":
    module.main()
