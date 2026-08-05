from pathlib import Path
import apply_seventy_first_pass_repairs as p

A = Path("PrimalitySheafVerification/Mock2_Advanced.lean")
F = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")


def edit(path, edits):
    s = path.read_text(encoding="utf-8")
    for old, new, label in edits:
        s, _ = p.replace_exact(s, old, new, 1, label)
    path.write_text(s, encoding="utf-8", newline="\n")


def main():
    edit(A, [
        ("      change Mono ((cyclicFreeComplex N).d 1 0)\n      rw [cyclicFreeComplex_d_one_zero,\n        ModuleCat.mono_iff_injective]\n      simpa using cyclicResolutionDifferential_injective N hN\n",
         "      change Mono ((cyclicFreeComplex N).d 1 0)\n      rw [cyclicFreeComplex_d_one_zero]\n      exact (ModuleCat.mono_iff_injective _).2\n        (cyclicResolutionDifferential_injective N hN)\n",
         "degree-one mono"),
        ("    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)\n      (by simp only [Category.id_comp, Category.comp_id])\n      (by simp only [Category.id_comp, Category.comp_id])\n",
         "    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)\n      (by\n        simp only [Category.id_comp, Category.comp_id]\n        exact (cyclicFreeComplex_d_one_zero N).symm)\n      (by\n        simp only [Category.id_comp, Category.comp_id]\n        exact (cyclicFreeAugmentation_f_zero N).symm)\n",
         "degree-zero short arrows"),
    ])
    edit(F, [
        ("  have hI : star (Complex.I) = -Complex.I := by simp\n  have hweight :\n      star (physicalExponent a * (heightC z)⁻¹) =\n        physicalExponent a * (heightC z)⁻¹ := by\n    simp only [star_mul', star_inv₀, conj_physicalExponent, conj_heightC]\n    ring\n  simp only [raiseRaw, lowerRaw, star_add, star_mul']\n  rw [hI, hweight]\n  field_simp [hh]\n  ring\n",
         "  simp only [raiseRaw, lowerRaw, star_add, star_mul', star_div,\n    Complex.conj_I, conj_physicalExponent, conj_heightC]\n  field_simp [hh]\n  ring\n",
         "Green division normalization"),
        ("  change\n    (fun w : ℍ => upperLift f (w : ℂ)) =ᶠ[nhds z]\n      (fun _ : ℍ => (0 : ℂ))\n  simpa [upperLift, Function.comp_def] using hz\n",
         "  change\n    (fun w : ℍ => upperLift f (w : ℂ)) =ᶠ[nhds z]\n      (fun _ : ℍ => (0 : ℂ))\n  filter_upwards [hz] with w hw\n  exact hw\n",
         "eventual zero transport"),
    ])
    return 0

if __name__ == "__main__": raise SystemExit(main())
