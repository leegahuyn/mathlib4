from __future__ import annotations

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "apply_three_hundred_seventh_pass_mock2_repairs.py"
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def load_pass307():
    spec = importlib.util.spec_from_file_location("mock2_pass307", SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    pass307 = load_pass307()
    result = pass307.main()
    if result != 0:
        return result

    text = M2.read_text(encoding="utf-8")
    old = """  proposition20_canonicalCover_zeroModel :
    Proposition20ActualQGaugeSpecialization.ActualProposition20Certificate
      Proposition20ActualQGaugeSpecialization.AdaptedGeometryCover.canonical
"""
    new = """  proposition20_canonicalCover_zeroModel :
    Nonempty
      (Proposition20ActualQGaugeSpecialization.ActualProposition20Certificate
        Proposition20ActualQGaugeSpecialization.AdaptedGeometryCover.canonical)
"""
    actual = text.count(old)
    print(
        "Mock2 proof-package static Proposition 20 certificate: "
        f"expected=1 actual={actual}"
    )
    if actual != 1:
        raise RuntimeError(
            "Mock2 proof-package static Proposition 20 certificate: "
            f"expected 1 match, found {actual}"
        )
    M2.write_text(text.replace(old, new), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
