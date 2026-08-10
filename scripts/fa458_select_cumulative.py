#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "scripts/fa457_select_true_first.py"


def main() -> None:
    spec = importlib.util.spec_from_file_location("fa457_selector_base", SOURCE)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load FA457 selector")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    module.BASE = ROOT / "build-logs/fa458-cumulative"
    module.COLLECTED = module.BASE / "collected"
    module.SELECTED = module.BASE / "selected"
    module.PREFIX = "fa458-candidate-"
    module.EXPECTED_VARIANTS = {
        "true_baseline",
        "cumulative_deriv",
        "tendsto_method",
        "tendsto_explicit",
        "tendsto_simpa",
        "tendsto_method_funprop",
        "tendsto_method_unfold_funprop",
        "tendsto_explicit_funprop",
    }
    module.main()


if __name__ == "__main__":
    main()
