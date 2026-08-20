from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def first_line(text: str) -> str:
    return text.splitlines()[0] if text.splitlines() else ""


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

    # These two audit rows only need a canonical universe instance of the
    # already universe-polymorphic public theorem.  Specializing the evidence
    # pointer does not alter either theorem's statement or implementation.
    text = replace_exact(
        text,
        "(@UnnumberedFormulaLedger.section7C_finiteTruncationsCauchy_proved)",
        "(@UnnumberedFormulaLedger.section7C_finiteTruncationsCauchy_proved.{0})",
        "Mock2 Advanced specialize finite-series Cauchy evidence",
    )
    text = replace_exact(
        text,
        "(@p02_supportSensitiveTruncation_correctedAndProved)",
        "(@p02_supportSensitiveTruncation_correctedAndProved.{0})",
        "Mock2 Advanced specialize support-sensitive truncation evidence",
    )

    # The expected function introduces the two G' typeclass arguments between
    # S and T.  Bind them explicitly, leaving them available to typeclass
    # inference in the actual universal-property theorem application.
    text = replace_exact(
        text,
        "      exact fun S T hT f => QGaugeVariableSheaf.factor_existsUnique S T hT f",
        "      exact fun S _ _ T hT f => QGaugeVariableSheaf.factor_existsUnique S T hT f",
        "Mock2 Advanced bind Definition12 target instances",
    )

    # The proposition is independent of the universe chosen for PUnit.  Pin a
    # canonical universe so the finite ClaimEvidence family closes without an
    # otherwise unconstrained level metavariable.
    text = replace_exact(
        text,
        "      ¬ Nonempty (PUnit → Empty)",
        "      ¬ Nonempty (PUnit.{0} → Empty)",
        "Mock2 Advanced pin Proposition15 PUnit universe",
    )

    M2A.write_text(text, encoding="utf-8")
    print("[pass311] Mock2_Advanced final four candidate errors repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
