from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def write(path: Path, before: str, after: str) -> None:
    if before != after:
        path.write_text(after, encoding="utf-8", newline="\n")


def repair_mock1() -> None:
    path = ROOT / "Mock1.lean"
    text = path.read_text(encoding="utf-8")
    old = text
    text = text.replace(
"""  unfold zmodGcdToTorProxyHom
  rw [← Int.cast_one, ZMod.lift_coe]
  rfl
""",
"""  unfold zmodGcdToTorProxyHom
  rw [← Int.cast_one, ZMod.lift_coe]
  change (1 : ℤ) • torProxyExplicitGenerator M N = torProxyExplicitGenerator M N
  simp
""", 1)
    write(path, old, text)


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = text

    text = text.replace(
"""/-- The concrete density formula for the hyperbolic measure. -/
set_option maxHeartbeats 800000 in
theorem hyperbolicMeasure_def :
""",
"""set_option maxHeartbeats 2000000 in
/-- The concrete density formula for the hyperbolic measure. -/
theorem hyperbolicMeasure_def :
""", 1)
    text = text.replace("  ring\n\n/-- The positive Gaussian tail is summable",
                        "  simp only [UpperHalfPlane.coe_im]\n  ring\n\n/-- The positive Gaussian tail is summable", 1)
    text = text.replace(
"""  change (u : H) ∈ closure (↑M.core : Set H)
  simpa only [Submodule.topologicalClosure_coe] using u.property
""",
"""  change (u : H) ∈ closure (↑M.core : Set H)
  simpa [weightedAutomorphicSobolev, Submodule.topologicalClosure_coe] using u.property
""", 1)
    text = text.replace("  refine Set.disjoint_left.mpr (fun τ h∞ h₀ => ?_)\n",
                        "  rw [Set.disjoint_left]\n  intro τ h∞ h₀\n", 1)
    text = text.replace("  refine Set.disjoint_left.mpr (fun τ h∞ h₁ => ?_)\n",
                        "  rw [Set.disjoint_left]\n  intro τ h∞ h₁\n", 1)
    text = text.replace("  refine Set.disjoint_left.mpr (fun τ h₀ h₁ => ?_)\n",
                        "  rw [Set.disjoint_left]\n  intro τ h₀ h₁\n", 1)
    text = text.replace(
"""theorem pairwise_disjoint_strictCuspHoroball :
    Pairwise (fun κ λ => Disjoint (strictCuspHoroball κ) (strictCuspHoroball λ)) := by
  intro κ λ hκλ
  cases κ <;> cases λ
""",
"""theorem pairwise_disjoint_strictCuspHoroball :
    Pairwise (fun κ κ' => Disjoint (strictCuspHoroball κ) (strictCuspHoroball κ')) := by
  intro κ κ' hκκ'
  cases κ <;> cases κ'
""", 1)
    text = text.replace("(hκλ rfl).elim", "(hκκ' rfl).elim")
    text = text.replace(
"""  rcases hK.bddAbove_image
      (continuous_cuspHeight Gamma2Cusp.infinity).continuousOn with
    ⟨Y∞, hY∞⟩
  rcases hK.bddAbove_image
      (continuous_cuspHeight Gamma2Cusp.zero).continuousOn with
    ⟨Y₀, hY₀⟩
  rcases hK.bddAbove_image
      (continuous_cuspHeight Gamma2Cusp.one).continuousOn with
    ⟨Y₁, hY₁⟩
""",
"""  obtain ⟨Y∞, hY∞⟩ := hK.bddAbove_image
    (continuous_cuspHeight Gamma2Cusp.infinity).continuousOn
  obtain ⟨Y₀, hY₀⟩ := hK.bddAbove_image
    (continuous_cuspHeight Gamma2Cusp.zero).continuousOn
  obtain ⟨Y₁, hY₁⟩ := hK.bddAbove_image
    (continuous_cuspHeight Gamma2Cusp.one).continuousOn
""", 1)
    write(path, old, text)


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    old = text

    text = text.replace("set_option maxRecDepth 10000 in\n", "")
    anchor = "namespace Mock2FA\n"
    if anchor in text and "set_option maxRecDepth 10000\n" not in text:
        text = text.replace(anchor, anchor + "\nset_option maxRecDepth 10000\n", 1)

    theorem_block = """theorem innerSLFlip_pairing [InnerProductSpace ℂ E] (u v : E) :
    antiDualPairing (innerSLFlip ℂ u) v = ⟪v, u⟫_ℂ :=
  by
    simpa only [antiDualPairing] using
      (innerSLFlip_apply_apply ℂ u v)
"""
    replacement = """end AntiDualAndWeakEquation

section InnerSLFlipPairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem innerSLFlip_pairing (u v : E) :
    antiDualPairing (innerSLFlip ℂ u) v = ⟪v, u⟫_ℂ := by
  simpa only [antiDualPairing] using
    (innerSLFlip_apply_apply ℂ u v)

end InnerSLFlipPairing

section AntiDualAndWeakEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
"""
    text = text.replace(theorem_block, replacement, 1)
    write(path, old, text)


def main() -> int:
    repair_mock1()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
