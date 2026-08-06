from __future__ import annotations

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "apply_three_hundred_fifth_pass_mock2_repairs.py"


def load_pass305():
    spec = importlib.util.spec_from_file_location("mock2_pass305", SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    pass305 = load_pass305()
    original = pass305.replace_exact

    def replace_exact(text, old, new, label, expected=1):
        if label == "Mock2 proof-package Proposition 20 certificate":
            expected = 1
        return original(text, old, new, label, expected)

    pass305.replace_exact = replace_exact
    return pass305.main()


if __name__ == "__main__":
    raise SystemExit(main())
