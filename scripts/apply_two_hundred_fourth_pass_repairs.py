from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(
    text: str, old: str, new: str, label: str, expected: int = 1
) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(
            f"{label}: expected exactly {expected} match(es), found {count}"
        )
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """abbrev SmoothQuotientCompactFunction := smoothQuotientCompactSubmodule

/-- Raising is a linear endomorphism of the smooth quotient-compact analytic
""",
        """abbrev SmoothQuotientCompactFunction := smoothQuotientCompactSubmodule

/-- Evaluate a smooth quotient-compact function without relying on a
multi-step coercion through `SmoothFunction`. -/
instance : CoeFun SmoothQuotientCompactFunction (fun _ => ℍ → ℂ) where
  coe f := (f.1 : ℍ → ℂ)

/-- Raising is a linear endomorphism of the smooth quotient-compact analytic
""",
        "FunctionalAnalysis add the direct function coercion for the analytic core",
    )
    fa = replace_exact(
        fa,
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [star_inv, hConjPow]
        field_simp [hjc]
""",
        """      Bw = star j ^ 2 *
          (star ((j ^ 2)⁻¹) * Bw) := by
        rw [hConjPow]
        field_simp [hjc]
""",
        "FunctionalAnalysis rewrite the conjugate square already exposed by elaboration",
    )
    fa = replace_exact(
        fa,
        """instance (n : ℤ) : Inhabited (InverseEtaFixedPhaseCore n) :=
  ⟨0⟩
""",
        """noncomputable instance (n : ℤ) : Inhabited (InverseEtaFixedPhaseCore n) :=
  ⟨0⟩
""",
        "FunctionalAnalysis mark fixed-phase core inhabitation noncomputable",
    )
    fa = replace_exact(
        fa,
        """instance {n : ℤ} :
    Coe (InverseEtaFixedPhaseCore n) SmoothQuotientCompactFunction :=
  ⟨toSmoothQuotientCompactFunction⟩
""",
        """noncomputable instance (n : ℤ) :
    Coe (InverseEtaFixedPhaseCore n) SmoothQuotientCompactFunction :=
  ⟨toSmoothQuotientCompactFunction⟩
""",
        "FunctionalAnalysis make the source index explicit in the core coercion",
    )
    fa = replace_exact(
        fa,
        """  toFun u := ⟨(u : SmoothQuotientCompactFunction), by
    simpa [IsInverseEtaPaperOrbitCovariant] using
      (u.2 FixedPhaseDifferentialWord.nil)⟩
""",
        """  toFun u := ⟨toSmoothQuotientCompactFunction u,
    (mem_inverseEtaFixedPhaseStableCoreSubmodule_iff n
      (toSmoothQuotientCompactFunction u)).1 u.2⟩
""",
        "FunctionalAnalysis obtain zeroth-word covariance through the membership equivalence",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
