from __future__ import annotations

from pathlib import Path

import apply_ninety_fifth_pass_repairs as pass95
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """def AdvancedClaimsIIPaperI2MahlerEval (n : Nat) : Int :=
  (Finset.sum Finset.univ
    (fun j : Fin 6 =>
      AdvancedClaimsIIPaperI2MahlerCoefficient j *
        mahlerBinomialBasis (j : Nat) n)) %
    (PrimePower AdvancedClaimsIIPaperI2Prime
      AdvancedClaimsIIPaperI2Precision : Int)
""",
        """def AdvancedClaimsIIPaperI2MahlerRawEval (n : Nat) : Int :=
  Finset.sum Finset.univ
    (fun j : Fin 6 =>
      AdvancedClaimsIIPaperI2MahlerCoefficient j *
        mahlerBinomialBasis (j : Nat) n)

def AdvancedClaimsIIPaperI2MahlerEval (n : Nat) : Int :=
  AdvancedClaimsIIPaperI2MahlerRawEval n %
    (PrimePower AdvancedClaimsIIPaperI2Prime
      AdvancedClaimsIIPaperI2Precision : Int)
""",
        1,
        "Mock1Advanced separate the raw Mahler sum from its mod-25 representative",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """def referenceAdvancedClaimsIIPaperI2MahlerBinomial :
    MahlerBinomialCertificate where
  p := AdvancedClaimsIIPaperI2Prime
  k := AdvancedClaimsIIPaperI2Precision
  length := 6
  target := AdvancedClaimsIIPaperI2MahlerEval
  coeff := AdvancedClaimsIIPaperI2MahlerCoefficient
  eval := AdvancedClaimsIIPaperI2MahlerEval
  eval_eq := by
    intro n
    rfl
  matches_target := by
    intro n
    exact finiteCongruence_refl _ _ _
""",
        """def referenceAdvancedClaimsIIPaperI2MahlerBinomial :
    MahlerBinomialCertificate where
  p := AdvancedClaimsIIPaperI2Prime
  k := AdvancedClaimsIIPaperI2Precision
  length := 6
  target := AdvancedClaimsIIPaperI2MahlerEval
  coeff := AdvancedClaimsIIPaperI2MahlerCoefficient
  eval := AdvancedClaimsIIPaperI2MahlerRawEval
  eval_eq := by
    intro n
    rfl
  matches_target := by
    intro n
    unfold FiniteCongruenceMod IntCongruent
    refine ⟨AdvancedClaimsIIPaperI2MahlerRawEval n /
      (PrimePower AdvancedClaimsIIPaperI2Prime
        AdvancedClaimsIIPaperI2Precision : Int), ?_⟩
    have h := Int.emod_add_ediv
      (AdvancedClaimsIIPaperI2MahlerRawEval n)
      (PrimePower AdvancedClaimsIIPaperI2Prime
        AdvancedClaimsIIPaperI2Precision : Int)
    unfold AdvancedClaimsIIPaperI2MahlerEval
    omega
""",
        1,
        "Mock1Advanced certify the raw Mahler sum against its residue target",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")

    text, changed = replace_exact(
        text,
        """  have hfirst :
      matrixWedge (matrixDifferential g.inverse) g.forward =
        -matrixWedge g.inverse (matrixDifferential g.forward) := by
    abel_nf at hsum ⊢
    exact hsum
""",
        """  have hfirst :
      matrixWedge (matrixDifferential g.inverse) g.forward =
        -matrixWedge g.inverse (matrixDifferential g.forward) := by
    calc
      matrixWedge (matrixDifferential g.inverse) g.forward =
          (matrixWedge (matrixDifferential g.inverse) g.forward +
            matrixWedge g.inverse (matrixDifferential g.forward)) -
              matrixWedge g.inverse (matrixDifferential g.forward) := by
        abel
      _ = -matrixWedge g.inverse (matrixDifferential g.forward) := by
        rw [hsum]
        abel
""",
        1,
        "Mock2 derive the inverse-differential summand by explicit additive cancellation",
    )

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def _replace_in_theorem(
    text: str, theorem: str, next_marker: str, old: str, new: str, label: str
) -> tuple[str, bool]:
    start = text.index(f"theorem {theorem}")
    end = text.index(next_marker, start)
    block = text[start:end]
    count = block.count(old)
    if count == 1:
        block = block.replace(old, new, 1)
        print(f"{label}: applied 1")
        return text[:start] + block + text[end:], True
    if count == 0 and new in block:
        print(f"{label}: already applied")
        return text, False
    raise RuntimeError(f"{label}: expected one scoped match, found {count}")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = _replace_in_theorem(
        text,
        "weightedAutomorphicSobolev_ae",
        "\n\n/-- The sum of the three stored graph-energy components.",
        "exact (M.core_equivariant v hv).isAE μ)",
        "exact (M.core_equivariant v hv).isAE)",
        "Mock2Advanced keep the ordinary half-weight measure implicit",
    )
    changed |= did

    text, did = _replace_in_theorem(
        text,
        "space_ae",
        "\n\n/-- Smooth compact-core test vectors.",
        "exact (M.core_equivariant v hv).isAE)",
        "exact (M.core_equivariant v hv).isAE μ)",
        "Mock2Advanced supply the inverse-half-weight measure explicitly",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """      (measurableSet_singleton.preimage
        Complex.measurable_re).nullMeasurableSet
""",
        """      (measurableSet_eq Complex.measurable_re
        measurable_const).nullMeasurableSet
""",
        1,
        "FunctionalAnalysis restore the working measurable equality description",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """  have hmove :
      ((gammaTwoCosetRep q₂)⁻¹ * (γ : SL(2, ℤ)) *
          gammaTwoCosetRep q₁) • z₁ = z₂ := by
    simp only [mul_smul]
    rw [hy_eq, ← hγ y, hxy, ← hx_eq, inv_smul_smul]
""",
        """  have hmove :
      ((gammaTwoCosetRep q₂)⁻¹ * (γ : SL(2, ℤ)) *
          gammaTwoCosetRep q₁) • z₁ = z₂ := by
    simp only [mul_smul]
    calc
      (gammaTwoCosetRep q₂)⁻¹ •
          (γ : SL(2, ℤ)) • gammaTwoCosetRep q₁ • z₁ =
          (gammaTwoCosetRep q₂)⁻¹ • (γ : SL(2, ℤ)) • y := by
        rw [hy_eq]
      _ = (gammaTwoCosetRep q₂)⁻¹ • a • y := by
        exact congrArg
          (fun t : ℍ => (gammaTwoCosetRep q₂)⁻¹ • t)
          (hγ y).symm
      _ = (gammaTwoCosetRep q₂)⁻¹ • x := by
        exact congrArg
          (fun t : ℍ => (gammaTwoCosetRep q₂)⁻¹ • t) hxy
      _ = (gammaTwoCosetRep q₂)⁻¹ • gammaTwoCosetRep q₂ • z₂ := by
        exact congrArg
          (fun t : ℍ => (gammaTwoCosetRep q₂)⁻¹ • t) hx_eq.symm
      _ = z₂ := by simp
""",
        1,
        "FunctionalAnalysis prove tile transport by four explicit action equalities",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass95.main()
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
