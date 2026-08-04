from __future__ import annotations

from pathlib import Path

import apply_sixty_ninth_pass_repairs as pass69

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass69.replace_exact


def _mem_proof(index: int) -> str:
    proof = "List.mem_cons.mpr (Or.inl rfl)"
    for _ in range(index):
        proof = f"List.mem_cons.mpr (Or.inr ({proof}))"
    return "  · exact " + proof


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    groups = [
        ("objectSchema", 4),
        ("t1t5", 8),
        ("spt", 5),
        ("kernel", 8),
        ("exact", 7),
        ("pAdic", 10),
        ("entropy", 9),
    ]
    total = 0
    for name, count in groups:
        start = text.index(f"theorem requirementOf_{name}_at")
        end = text.index("\n\ntheorem ", start)
        region = text[start:end]
        if region.count("  · decide") == count:
            for index in range(count):
                region = region.replace("  · decide", _mem_proof(index), 1)
            text = text[:start] + region + text[end:]
            total += count
            changed = True
        elif "List.mem_cons.mpr" in region and "  · decide" not in region:
            total += count
        else:
            raise RuntimeError(
                f"Mock1Advanced {name}: expected {count} decidable branches")
    if total != 51:
        raise RuntimeError(f"Mock1Advanced expected 51 membership branches, got {total}")
    print("Mock1Advanced construct all 51 requirement memberships explicitly: applied/already applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    rw [map_zero]
    exact hz
""",
            """  have hz0 : z = 0 := by
    change (M : ℤ) * (z : ℤ) = 0 at hz
    change (z : ℤ) = 0
    exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hM)
""",
            "Mock2 prove degree-one exactness directly in the integer carrier",
        ),
        (
            """      rw [tensorResolutionComplex_d_two_one]
      rw [zero_comp])
""",
            """      rw [tensorResolutionComplex_d_two_one]
      rw [comp_zero])
""",
            "Mock2 use comp_zero for a morphism followed by zero",
        ),
        (
            """    { predicate_restriction_stable := fun hUV hA =>
        lemma6_1_covariance_restrict F Covariant hCov hUV hA
""",
            """    { predicate_restriction_stable := fun hUV {A} hA =>
        lemma6_1_covariance_restrict F Covariant hCov hUV hA
""",
            "Mock2 bind the implicit covariant section in the Lemma 6.1 certificate",
        ),
        (
            """      lemma6_1 := fun hVU hA =>
        lemma6_1_restriction_stability F Covariant hCov hVU hA
""",
            """      lemma6_1 := fun hVU {A} hA =>
        lemma6_1_restriction_stability F Covariant hCov hVU hA
""",
            "Mock2 bind the implicit section in the Aq certificate",
        ),
        (
            """  obtain ⟨x, hx⟩ := hF.gluing_exists C s hs
""",
            """  obtain ⟨x, hx⟩ := IsSheafLike.gluing_exists hF C s hs
""",
            "Mock2 call the gluing-existence projection explicitly",
        ),
        (
            """  exact hF.gluing_unique C s hs hy hx
""",
            """  exact IsSheafLike.gluing_unique hF C s hs hy hx
""",
            "Mock2 call the gluing-uniqueness projection explicitly",
        ),
        (
            """    (hF.gluing_exists C e.1 (F.coverEqualizer_compatible C e))
""",
            """    (IsSheafLike.gluing_exists hF C e.1
      (F.coverEqualizer_compatible C e))
""",
            "Mock2 use explicit gluing existence in glue",
        ),
        (
            """    (hF.gluing_exists C e.1 (F.coverEqualizer_compatible C e))
""",
            """    (IsSheafLike.gluing_exists hF C e.1
      (F.coverEqualizer_compatible C e))
""",
            "Mock2 use explicit gluing existence in glue_isGluing",
        ),
        (
            """  hF.gluing_unique (OpenCoverData.wholeSpace U hcover) s hs hx hy
""",
            """  IsSheafLike.gluing_unique hF
    (OpenCoverData.wholeSpace U hcover) s hs hx hy
""",
            "Mock2 use explicit global gluing uniqueness",
        ),
        (
            """  hF.existsUnique_gluing (OpenCoverData.wholeSpace U hcover) s hs
""",
            """  IsSheafLike.existsUnique_gluing hF
    (OpenCoverData.wholeSpace U hcover) s hs
""",
            "Mock2 use explicit unique-gluing theorem",
        ),
        (
            """  hF.global_gluing_unique U hcover e.1
""",
            """  IsSheafLike.global_gluing_unique hF U hcover e.1
""",
            "Mock2 use explicit selected-global-gluing uniqueness",
        ),
    ]
    for old, new, label in replacements:
        expected = 2 if label == "Mock2 use explicit gluing existence in glue" else 1
        text, did = replace_exact(text, old, new, expected, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_exact(
        text,
        """    intro ι U V hVU hcover s hcompat
    choose index hindex using fun x : U =>
""",
        """    intro ι U V hVU hcover s hcompat
    change (i : ι) → sections (X := X) (Fiber := Fiber) (V i) at s
    choose index hindex using fun x : U =>
""",
        1,
        "Mock2Advanced normalize the gluing family to concrete sections",
    )
    changed |= did

    text, did = replace_exact(
        text,
        """      · funext τ
        simp only [sqrtFactor_mul, gamma2Act_mul, mul_assoc])
""",
        """      · funext τ
        simp only [sqrtFactor_mul, matrix_mul, gamma2Act_mul, mul_assoc])
""",
        1,
        "Mock2Advanced expose matrix multiplication in sqrt-factor associativity",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2] <;> ring
""",
            """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
""",
            "FunctionalAnalysis cancel the intermediate eta value explicitly",
        ),
        (
            """  have hscale : star (m.scale z : ℂ) = (m.scale z : ℂ) := by
    change Complex.conj (m.scale z : ℂ) = (m.scale z : ℂ)
    exact Complex.conj_ofReal (m.scale z)
""",
            """  have hscale : star (m.scale z : ℂ) = (m.scale z : ℂ) := by
    simp
""",
            "FunctionalAnalysis simplify star on a real complex scalar",
        ),
        (
            """    simpa only [Complex.ofReal_mul] using
""",
            """    simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using
""",
            "FunctionalAnalysis transport the real norm square through complex coercion",
        ),
        (
            """def gammaTwoEffectiveElement (γ : GammaTwo) : GammaTwoEffective :=
""",
            """noncomputable def gammaTwoEffectiveElement (γ : GammaTwo) : GammaTwoEffective :=
""",
            "FunctionalAnalysis mark the effective-action element noncomputable",
        ),
        (
            """def gammaTwoQuotientMk : ℍ → GammaTwoQuotient :=
""",
            """noncomputable def gammaTwoQuotientMk : ℍ → GammaTwoQuotient :=
""",
            "FunctionalAnalysis mark the orbit quotient map noncomputable",
        ),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
