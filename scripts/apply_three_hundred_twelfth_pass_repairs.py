from __future__ import annotations

# Retry marker: the previous pass-312 Matrix attempt never reached checkout or Lean
# because GitHub Actions could not resolve pinned action downloads (HTTP 503).

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def first_line(text: str) -> str:
    lines = text.splitlines()
    return lines[0] if lines else ""


def replace_exact(
    text: str,
    old: str,
    new: str,
    label: str,
    expected: int = 1,
) -> str:
    actual = text.count(old)
    print(
        f"{label}: expected={expected} actual={actual} "
        f"before={first_line(old)!r} after={first_line(new)!r}"
    )
    if actual != expected:
        raise RuntimeError(
            f"{label}: expected {expected} matches, found {actual}"
        )
    return text.replace(old, new)


def main() -> int:
    text = M2A.read_text(encoding="utf-8")

    text = replace_exact(
        text,
        "(@UnnumberedFormulaLedger.section7C_finiteTruncationsConverge_proved)",
        "(@UnnumberedFormulaLedger.section7C_finiteTruncationsConverge_proved.{0})",
        "Mock2 Advanced specialize finite-series convergence evidence",
    )
    text = replace_exact(
        text,
        "(@p07_parallelMockEnergyZero_correctedAndProved)",
        "(@p07_parallelMockEnergyZero_correctedAndProved.{0})",
        "Mock2 Advanced specialize parallel-energy evidence",
    )

    M2A.write_text(text, encoding="utf-8")
    print("[pass312] Mock2_Advanced final two universe witnesses specialized")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
