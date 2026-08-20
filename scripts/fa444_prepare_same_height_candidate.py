#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from types import ModuleType

ROOT = Path.cwd()
ORIGINAL = ROOT / "scripts/fa442_prepare_same_height_candidate.py"


def load_original() -> ModuleType:
    spec = importlib.util.spec_from_file_location("fa442_prepare_original", ORIGINAL)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load candidate generator: {ORIGINAL}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main() -> None:
    module = load_original()

    def apply_upper_half_plane(text: str) -> tuple[str, dict]:
        records: list[dict] = []
        text, count = module.replace_exact(
            text,
            "    hcomplex.subtype_mk _\n",
            "    hcomplex.upperHalfPlaneMk _\n",
        )
        records.append({"repair": "upperHalfPlaneMk", "applied": count})

        # The authoritative baseline contains four six-space-indented
        # `apply Subtype.ext` lines. Only the one in the hbase'.congr proof is
        # an UpperHalfPlane structure conversion; global replacement is invalid.
        old = (
            "    hbase'.congr (fun t => by\n"
            "      apply Subtype.ext\n"
            "      apply Complex.ext <;> simp)\n"
        )
        new = (
            "    hbase'.congr (fun t => by\n"
            "      apply UpperHalfPlane.ext\n"
            "      apply Complex.ext <;> simp)\n"
        )
        text, count = module.replace_exact(text, old, new)
        records.append(
            {
                "repair": "UpperHalfPlane.ext_contextual",
                "applied": count,
            }
        )
        return text, {"repair": "upper_half_plane_cluster", "details": records}

    module.apply_upper_half_plane = apply_upper_half_plane
    module.main()


if __name__ == "__main__":
    main()
