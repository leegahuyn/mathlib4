from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(path: Path, old: str, new: str, label: str) -> bool:
    text = path.read_text(encoding="utf-8")
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied or source changed")
        return False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    path.write_text(text.replace(old, new), encoding="utf-8", newline="\n")
    print(f"{label}: applied")
    return True


def main() -> int:
    changed = False

    spt2 = ROOT / "Spt2.lean"
    changed = replace_once(
        spt2,
        """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]

noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    ((quotientSpanCotangentEquivKer f).trans
      (quotientExtensionCotangentEquivKer f))
""",
        """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]
  exact LinearEquiv.refl K _

noncomputable def quotientConormalEquivForward (f : K[X]) (hf : f ≠ 0) :
    (K[X] ⧸ Ideal.span ({f} : Set K[X])) ≃ₗ[K]
      (quotientExtension f).Cotangent :=
  ((principalCotangentQuotEquiv (R := K[X]) (poly := f) hf).restrictScalars K).trans
    ((quotientSpanCotangentEquivKer f).trans
      (quotientExtensionCotangentEquivKer f))
""",
        "Spt2 make the conormal ideal transport an explicit reflexive equivalence",
    ) or changed

    changed = replace_once(
        spt2,
        """      rw [← principalAQH1Model_cotangentComplex_kernel_iff f hf]
      exact y.property⟩
""",
        """      rw [← principalAQH1Model_cotangentComplex_kernel_iff f hf]
      simpa only [LinearMap.mem_ker, LinearEquiv.apply_symm_apply] using y.property⟩
""",
        "Spt2 cancel the conormal equivalence in the stored kernel witness",
    ) or changed

    spt3 = ROOT / "Spt3.lean"
    changed = replace_once(
        spt3,
        """    s = t := by
  have hId := h (𝟙 U)
  rw [Functor.map_id] at hId
  change s = t at hId
  exact hId
""",
        """    s = t := by
  have hId := h (𝟙 U)
  rw [(amalgam Fnum Fmod Fpadic FEC).toFunctor.map_id] at hId
  simpa using hId
""",
        "Spt3 use the concrete functor map-id theorem",
    ) or changed

    changed = replace_once(
        spt3,
        """  obtain ⟨V, f, hf, hxV⟩ := hcov x hx
  simpa [RepointedConst_map_apply] using hf (PLift.up ⟨x, hxV⟩)
""",
        """  obtain ⟨V, f, hf, hxV⟩ := hcov x hx
  have hmem := hf (PLift.up ⟨x, hxV⟩)
  rw [RepointedConst_map_apply] at hmem
  have heq :
      s (liftNE (leOfHom f) (PLift.up ⟨x, hxV⟩)) = s p :=
    RepointedConst_const s _ _
  rwa [heq] at hmem
""",
        "Spt3 transport predicate membership across proof-irrelevant points",
    ) or changed

    changed = replace_once(
        spt3,
        """  obtain ⟨V, f, hf, hxV⟩ := hcov x hx
  rw [hconst U.unop ⟨x, hx⟩, ← hconst V ⟨x, hxV⟩]
  simpa [RepointedConst_map_apply] using hf (PLift.up ⟨x, hxV⟩)
""",
        """  obtain ⟨V, f, hf, hxV⟩ := hcov x hx
  have hmem := hf (PLift.up ⟨x, hxV⟩)
  rw [RepointedConst_map_apply] at hmem
  rw [hconst V ⟨x, hxV⟩] at hmem
  rw [hconst U.unop ⟨x, hx⟩]
  have heq :
      s (liftNE (leOfHom f) (PLift.up ⟨x, hxV⟩)) = s p :=
    RepointedConst_const s _ _
  rwa [heq] at hmem
""",
        "Spt3 transport variable-layer membership across proof-irrelevant points",
    ) or changed

    spt4 = ROOT / "Spt4.lean"
    changed = replace_once(
        spt4,
        """theorem resC_d_succ_zero (N j : ℕ) : (resC N).d (j + 1 + 1) (j + 1) = 0 := by
  simpa [resC, df] using
    (ChainComplex.of_d Xf (df N)
      (fun n => by
        have : df N (n + 1) = 0 := rfl
        rw [this, zero_comp]) (j + 1))
""",
        """theorem resC_d_succ_zero (N j : ℕ) : (resC N).d (j + 1 + 1) (j + 1) = 0 := by
  change ChainComplex.of.d Xf (df N) (j + 1 + 1) (j + 1) = 0
  rw [ChainComplex.of_d]
  rfl
""",
        "Spt4 compute higher resolution differential without simplifier expansion",
    ) or changed

    print("Final Spt2/Spt3/Spt4 repairs changed sources." if changed else "No final SPT changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
