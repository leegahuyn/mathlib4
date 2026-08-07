from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "d9bce9ec296c799fe144786111da5a6e8f7f0232f55fd34df9cf09be8b140b4e"
EXPECTED_OUTPUT_SHA256 = "199fa4c17559a26fd5dfa5524db0a1eab46493fc33786608eef040fb7c05a40b"

REPLACEMENTS = [
    (
        "fixed-phase graph-core additive instance",
        "  exact inferInstanceAs (AddCommGroup ↥(inverseEtaFixedPhaseStableCoreSubmodule n))",
        "  exact Submodule.addCommGroup",
    ),
    (
        "fixed-phase graph-core complex module instance",
        "  exact inferInstanceAs (Module ℂ ↥(inverseEtaFixedPhaseStableCoreSubmodule n))",
        "  exact Submodule.module",
    ),
    (
        "fixed-phase density additive instance",
        "  exact inferInstanceAs (AddCommGroup ↥(fixedPhaseCoreSubmodule n))",
        "  exact Submodule.addCommGroup",
    ),
    (
        "fixed-phase density complex module instance",
        "  exact inferInstanceAs (Module ℂ ↥(fixedPhaseCoreSubmodule n))",
        "  exact Submodule.module",
    ),
    (
        "compact covariance multiplication order",
        "  simpa only [map_mul] using hCov",
        "  simpa only [map_mul, mul_assoc, mul_left_comm, mul_comm] using hCov",
    ),
    (
        "full covariance multiplication order",
        "  simpa only [map_mul] using\n    fixedPhaseEuclideanCovariance (n := n) (g := g) (u := u) (z := z)",
        "  simpa only [map_mul, mul_assoc, mul_left_comm, mul_comm] using\n    fixedPhaseEuclideanCovariance (n := n) (g := g) (u := u) (z := z)",
    ),
]


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass342] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass342 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    for name, old, new in REPLACEMENTS:
        count = text.count(old)
        print(f"{name}: expected=1 actual={count}")
        if count != 1:
            raise RuntimeError(f"{name}: expected one occurrence, found {count}")
        text = text.replace(old, new)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass342 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass342] explicit subtype instances and covariance normalizations applied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
