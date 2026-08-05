from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """  have hDelta :=
    SlashInvariantForm.slash_action_eqn_SL''
      CuspForm.discriminant
      (CongruenceSubgroup.mem_Gamma_one γ.1) τ
  simpa [etaValue, ModularForm.discriminant, denominator, gammaGL] using hDelta
""",
        """  have hmem :
      gammaGL γ ∈ (Matrix.SpecialLinearGroup.mapGL ℝ).range := by
    exact ⟨γ.1, rfl⟩
  have hDelta :=
    SlashInvariantForm.slash_action_eqn''
      CuspForm.discriminant hmem τ
  simpa [etaValue, ModularForm.discriminant, denominator, gammaGL] using hDelta
""",
        "Mock2 use the discriminant law on the full special-linear image",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """theorem isCompact_repTruncated (r : Gamma2Rep) (Y : ℝ) :
    IsCompact (repTruncated r Y) := by
  change IsCompact
    ((Homeomorph.smul (repMatrix r) :
        UpperHalfPlane ≃ₜ UpperHalfPlane) ⁻¹'
      ModularGroup.truncatedFundamentalDomain Y)
  exact
    (Homeomorph.smul (repMatrix r) :
      UpperHalfPlane ≃ₜ UpperHalfPlane).isCompact_preimage.mpr
        (ModularGroup.isCompact_truncatedFundamentalDomain Y)
""",
        """theorem isCompact_repTruncated (r : Gamma2Rep) (Y : ℝ) :
    IsCompact (repTruncated r Y) := by
  let g : GL (Fin 2) ℝ :=
    ((repMatrix r : IntegralSpecialLinear) : GL (Fin 2) ℝ)
  change IsCompact
    ((Homeomorph.smul g : UpperHalfPlane ≃ₜ UpperHalfPlane) ⁻¹'
      ModularGroup.truncatedFundamentalDomain Y)
  exact
    (Homeomorph.smul g : UpperHalfPlane ≃ₜ UpperHalfPlane).isCompact_preimage.mpr
      (ModularGroup.isCompact_truncatedFundamentalDomain Y)
""",
        "Mock2 Advanced express the compact pullback through the real GL action",
    )
    m2a = replace_exact(
        m2a,
        """    IsOpen U ∧
    ContDiffOn ℝ ∞ curve U ∧
""",
        """    IsOpen U ∧
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) curve U ∧
""",
        "Mock2 Advanced make the infinite differentiability order explicit",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """        rw [← hConjPow]
        field_simp [hjc]
""",
        """        rw [← hConjPow]
        field_simp [hjc]
        ring
""",
        "FunctionalAnalysis close the conjugate-square cancellation by commutativity",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
