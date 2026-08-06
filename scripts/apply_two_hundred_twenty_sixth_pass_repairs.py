from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """  LieGroup.of_le (I := I_G) (G := G)
    (show minSmoothness ℂ 3 ≤ (∞ : ℕ∞ω) from le_top)
""",
        """  LieGroup.of_le (I := I_G) (G := G)
    ((inferInstance : ENat.LEInfty (minSmoothness ℂ 3)).out)
""",
        "Mock2 use the registered finite-smoothness bound below infinity",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """      rw [(Homeomorph.smul gR).preimage_frontier s]
      simpa [gR, realGL_smul] using hτfrontier
""",
        """      rw [(Homeomorph.smul gR).preimage_frontier s]
      change τ ∈ frontier ((fun w : UpperHalfPlane => gR • w) ⁻¹' s)
      simpa [gR, realGL_smul] using hτfrontier
""",
        "Mock2_Advanced expose the smul function after frontier pullback",
    )
    m2a = replace_exact(
        m2a,
        """      rw [(Homeomorph.smul gR).preimage_frontier ModularGroup.fd]
      simpa [gR, realGL_smul] using hτfrontier
""",
        """      rw [(Homeomorph.smul gR).preimage_frontier ModularGroup.fd]
      change τ ∈ frontier
        ((fun w : UpperHalfPlane => gR • w) ⁻¹' ModularGroup.fd)
      simpa [gR, realGL_smul] using hτfrontier
""",
        "Mock2_Advanced expose the standard smul function after frontier pullback",
    )
    m2a = replace_exact(
        m2a,
        """  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro τ hτ
  change cuspHeight κ τ = Y at hτ
  exact (not_lt_of_ge hY) (hτ ▸ cuspHeight_pos κ τ)
""",
        """  ext τ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hτ
  change cuspHeight κ τ = Y at hτ
  exact (not_lt_of_ge hY) (hτ ▸ cuspHeight_pos κ τ)
""",
        "Mock2_Advanced prove the empty cusp level by extensionality",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  rw [fderiv_rpowScale_apply_of_im_pos p hw]
  simp only [directionalDerivative_apply]
""",
        """  rw [fderiv_rpowScale_apply_of_im_pos p hw]
  simp only [directionalDerivative_apply]
  ring
""",
        "FunctionalAnalysis close the weighted derivative by commutative normalization",
    )
    fa = replace_exact(
        fa,
        """    · exact (hf w hw).contDiffAt.mul v.contDiff.contDiffAt
""",
        """    · exact ((hf w hw).contDiffAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).mul
        v.contDiff.contDiffAt
""",
        "FunctionalAnalysis supply the open upper-half-plane neighbourhood",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
