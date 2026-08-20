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


def repair_spt2() -> bool:
    path = ROOT / "Spt2.lean"
    changed = False

    changed = replace_once(
        path,
        """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]
""",
        """noncomputable def quotientSpanCotangentEquivKer (f : K[X]) :
    (Ideal.span ({f} : Set K[X])).Cotangent ≃ₗ[K]
      (quotientExtension f).ker.Cotangent := by
  rw [quotientExtension_ker]
  exact LinearEquiv.refl K _
""",
        "Spt2 finish rewritten cotangent equivalence",
    ) or changed

    changed = replace_once(
        path,
        """  ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  unfold principalCotangentQuotEquiv quotientExtensionCotangentEquivKer
  change (Algebra.Extension.Cotangent.of
      ((Ideal.cotangentEquivOfEq (quotientExtension_ker f).symm)
        ((principalCotangentQuotMap f)
          ((Ideal.Quotient.mk (Ideal.span ({f} : Set K[X]))) a)))).val =
    (Algebra.Extension.Cotangent.mk
      (P := quotientExtension f)
      ⟨a * f, by
        rw [quotientExtension_ker]
        exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩).val
  rw [hmap]
  simp [Algebra.Extension.Cotangent.val_mk, Algebra.Extension.Cotangent.val_of]
  rfl
""",
        """  ext
  simp only [quotientConormalEquivForward, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  unfold principalCotangentQuotEquiv quotientExtensionCotangentEquivKer
  rw [hmap]
  simp [quotientSpanCotangentEquivKer, quotientExtension_ker,
    Algebra.Extension.Cotangent.val_mk, Algebra.Extension.Cotangent.val_of]
""",
        "Spt2 compute transported cotangent generator",
    ) or changed

    changed = replace_once(
        path,
        """      rw [← principalAQH1Model_cotangentComplex_kernel_iff f hf]
      exact y.property⟩
""",
        """      rw [← principalAQH1Model_cotangentComplex_kernel_iff f hf]
      simpa using y.property⟩
""",
        "Spt2 simplify equivalence apply-symm-apply in kernel witness",
    ) or changed

    return changed


def repair_spt3() -> bool:
    path = ROOT / "Spt3.lean"
    changed = False

    changed = replace_once(
        path,
        """    s = t := by
  have hId := h (𝟙 U)
  rw [Functor.map_id] at hId
  change s = t at hId
  exact hId
""",
        """    s = t := by
  have hId := h (𝟙 U)
  have hmap :
      (amalgam Fnum Fmod Fpadic FEC).toFunctor.map (𝟙 U) = 𝟙 _ := by
    simpa using (amalgam Fnum Fmod Fpadic FEC).toFunctor.map_id U
  rw [hmap] at hId
  simpa using hId
""",
        "Spt3 rewrite the bundled identity morphism before evaluation",
    ) or changed

    changed = replace_once(
        path,
        """  obtain ⟨V, f, hf, hxV⟩ := hcov x hx
  simpa [RepointedConst_map_apply] using hf (PLift.up ⟨x, hxV⟩)
""",
        """  obtain ⟨V, f, hf, hxV⟩ := hcov x hx
  have hp :
      liftNE (leOfHom f.unop) (PLift.up ⟨x, hxV⟩) = p :=
    plift_prop_subsingleton _ _
  rw [← hp]
  simpa [RepointedConst_map_apply] using hf (PLift.up ⟨x, hxV⟩)
""",
        "Spt3 identify proof-irrelevant nonempty witnesses in predLayer",
    ) or changed

    changed = replace_once(
        path,
        """  obtain ⟨V, f, hf, hxV⟩ := hcov x hx
  rw [hconst U.unop ⟨x, hx⟩, ← hconst V ⟨x, hxV⟩]
  simpa [RepointedConst_map_apply] using hf (PLift.up ⟨x, hxV⟩)
""",
        """  obtain ⟨V, f, hf, hxV⟩ := hcov x hx
  rw [hconst U.unop ⟨x, hx⟩, ← hconst V ⟨x, hxV⟩]
  have hp :
      liftNE (leOfHom f.unop) (PLift.up ⟨x, hxV⟩) = p :=
    plift_prop_subsingleton _ _
  rw [← hp]
  simpa [RepointedConst_map_apply] using hf (PLift.up ⟨x, hxV⟩)
""",
        "Spt3 identify proof-irrelevant witnesses in variable predLayer",
    ) or changed

    return changed


def repair_spt4() -> bool:
    path = ROOT / "Spt4.lean"
    return replace_once(
        path,
        """theorem resC_d_succ_zero (N j : ℕ) : (resC N).d (j + 1 + 1) (j + 1) = 0 := by
  simpa [resC, df] using
""",
        """set_option maxHeartbeats 800000 in
theorem resC_d_succ_zero (N j : ℕ) : (resC N).d (j + 1 + 1) (j + 1) = 0 := by
  simpa [resC, df] using
""",
        "Spt4 local heartbeat budget for general higher differential",
    )


def main() -> int:
    changed = repair_spt2()
    changed = repair_spt3() or changed
    changed = repair_spt4() or changed
    print("Remaining Spt repairs changed sources." if changed else "No remaining Spt changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
