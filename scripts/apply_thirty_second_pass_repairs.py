from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def nested_mem(heads: list[str]) -> str:
    proof = "List.Mem.head _"
    for _ in range(len(heads) - 1):
        proof = f"List.Mem.tail _ ({proof})"
    return proof


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  all_rows_certified := by
    intro row hrow
    simp only [referenceOLSRows, List.mem_cons, List.mem_singleton] at hrow
    rcases hrow with hα | hrest
    · subst row
      exact ⟨referenceAlphaOLSRow.table_number_at,
        referenceAlphaOLSRow.estimate_mem_at,
        referenceAlphaOLSRow.mode_diagnostic_at⟩
    · rcases hrest with hβ | hrest
      · subst row
        exact ⟨referenceBetaOLSRow.table_number_at,
          referenceBetaOLSRow.estimate_mem_at,
          referenceBetaOLSRow.mode_diagnostic_at⟩
      · rcases hrest with hγ | hrest
        · subst row
          exact ⟨referenceGammaOLSRow.table_number_at,
            referenceGammaOLSRow.estimate_mem_at,
            referenceGammaOLSRow.mode_diagnostic_at⟩
        · rcases hrest with hc | hrss
          · subst row
            exact ⟨referenceCeffOLSRow.table_number_at,
              referenceCeffOLSRow.estimate_mem_at,
              referenceCeffOLSRow.mode_diagnostic_at⟩
          · subst row
            exact ⟨referenceRSSOLSRow.table_number_at,
              referenceRSSOLSRow.estimate_mem_at,
              referenceRSSOLSRow.mode_diagnostic_at⟩
"""
    new = """  all_rows_certified := by
    intro row hrow
    cases hrow with
    | head _ =>
        exact ⟨referenceAlphaOLSRow.table_number_at,
          referenceAlphaOLSRow.estimate_mem_at,
          referenceAlphaOLSRow.mode_diagnostic_at⟩
    | tail _ hrow =>
      cases hrow with
      | head _ =>
          exact ⟨referenceBetaOLSRow.table_number_at,
            referenceBetaOLSRow.estimate_mem_at,
            referenceBetaOLSRow.mode_diagnostic_at⟩
      | tail _ hrow =>
        cases hrow with
        | head _ =>
            exact ⟨referenceGammaOLSRow.table_number_at,
              referenceGammaOLSRow.estimate_mem_at,
              referenceGammaOLSRow.mode_diagnostic_at⟩
        | tail _ hrow =>
          cases hrow with
          | head _ =>
              exact ⟨referenceCeffOLSRow.table_number_at,
                referenceCeffOLSRow.estimate_mem_at,
                referenceCeffOLSRow.mode_diagnostic_at⟩
          | tail _ hrow =>
            cases hrow with
            | head _ =>
                exact ⟨referenceRSSOLSRow.table_number_at,
                  referenceRSSOLSRow.estimate_mem_at,
                  referenceRSSOLSRow.mode_diagnostic_at⟩
            | tail _ h => cases h
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced prove OLS row certification from List.Mem constructors")
    changed |= did

    old = """  profile_negative := by
    intro p hp
    have hp' : p = ((-1 : ℤ), (1 : ℚ)) := by
      simpa only [referenceT1PolarProfile, List.mem_singleton] using hp
    subst p
    norm_num
"""
    new = """  profile_negative := by
    intro p hp
    change List.Mem p [((-1 : ℤ), (1 : ℚ))] at hp
    cases hp with
    | head _ => norm_num
    | tail _ h => cases h
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced prove T1 polar negativity structurally")
    changed |= did

    old = """  profile_negative := by
    intro p hp
    have hp' : p = ((-2 : ℤ), (1 : ℚ)) ∨
        p = ((-1 : ℤ), (1 : ℚ)) := by
      simpa only [referenceT2PolarProfile, List.mem_cons,
        List.mem_singleton] using hp
    rcases hp' with rfl | rfl <;> norm_num
"""
    new = """  profile_negative := by
    intro p hp
    change List.Mem p [((-2 : ℤ), (1 : ℚ)), ((-1 : ℤ), (1 : ℚ))] at hp
    cases hp with
    | head _ => norm_num
    | tail _ hp =>
      cases hp with
      | head _ => norm_num
      | tail _ h => cases h
"""
    text, did = replace_once(text, old, new,
        "Mock1Advanced prove T2 polar negativity structurally")
    changed |= did

    text, did = replace_once(text,
        """  residual_mem_diagnostic := by simp
  residual_not_mem_theorem := by simp
""",
        """  residual_mem_diagnostic := List.Mem.head _
  residual_not_mem_theorem := by decide
""",
        "Mock1Advanced certify the residual-table classification directly")
    changed |= did

    beta_names = [
        "unfoldingIdentity", "betaOneNormalization", "archimedeanScalar",
        "yIntegralNormalization", "rademacherLayerLink",
        "paperYIntegralValueBound", "paperScalarCoefficientFormula",
    ]
    beta_cases = [f"  | {name} => exact {nested_mem(beta_names[:i+1])}" for i, name in enumerate(beta_names)]
    old = """theorem mem_all (r : BetaArchimedeanDRequirement) :
    List.Mem r all := by
  cases r <;> decide
"""
    new = "theorem mem_all (r : BetaArchimedeanDRequirement) :\n    List.Mem r all := by\n  cases r with\n" + "\n".join(beta_cases) + "\n"
    text, did = replace_once(text, old, new,
        "Mock1Advanced prove the beta-archimedean registry structurally")
    changed |= did

    text, did = replace_once(text,
        "  normalizedValue_eq_value := by norm_num\n",
        "  normalizedValue_eq_value := by\n    norm_num [referenceArchimedeanIntegralCert]\n",
        "Mock1Advanced unfold the normalized archimedean value")
    changed |= did

    text, did = replace_once(text,
        """  scalar_link := by
    norm_num
""",
        """  scalar_link := by
    norm_num [referenceArchimedeanScalarRecord]
""",
        "Mock1Advanced unfold the archimedean scalar record")
    changed |= did

    text, did = replace_once(text,
        """  rademacher_link := by
    intro n
    simp [referenceNormalizedArchCoeff, referenceNormalizedArchRademacher]
""",
        """  rademacher_link := by
    intro n
    rfl
""",
        "Mock1Advanced compute the normalized Rademacher link definitionally")
    changed |= did

    exact_names = [
        "coefficientSeparationBoundary", "thetaCoefficientFiniteCertificate",
        "inducedCharacterFiniteCertificate", "spectralKloostermanExpansionCertificate",
        "localEulerDecompositionCertificate", "rootNumberFilterCertificate",
        "exactCoefficientLValueBoundary", "paperThetaCoefficientTable",
        "paperSpectralKloostermanData", "paperLocalEulerRootNumberLValueInput",
        "namedAnalyticBoundary", "finiteResidueKloostermanSum",
    ]
    exact_cases = [f"  | {name} => exact {nested_mem(exact_names[:i+1])}" for i, name in enumerate(exact_names)]
    old = """theorem mem_all (r : ExactCoefficientERequirement) :
    List.Mem r all := by
  cases r <;> decide
"""
    new = "theorem mem_all (r : ExactCoefficientERequirement) :\n    List.Mem r all := by\n  cases r with\n" + "\n".join(exact_cases) + "\n"
    text, did = replace_once(text, old, new,
        "Mock1Advanced prove the exact-coefficient registry structurally")
    changed |= did

    text, did = replace_once(text,
        """  all_residues_lt_modulus := by
    intro r hr
    simp at hr
    subst r
    decide
""",
        """  all_residues_lt_modulus := by
    intro r hr
    cases hr with
    | head _ => decide
    | tail _ h => cases h
""",
        "Mock1Advanced discharge the singleton residue bound structurally")
    changed |= did

    old = """theorem reference_exact_coefficient_e_checklist :
"""
    start = text.find(old)
    if start >= 0:
        proof_start = text.find(" :=\n", start)
        end = text.find("\n\nend Mock1Advanced", proof_start)
        if proof_start >= 0 and end >= 0:
            statement = text[start:proof_start + 4]
            proof = """by
  exact ⟨
    (fun r => referenceExactCoefficientECompletionCertificate.covers_at r),
    (fun n => referenceExactCoefficientECompletionCertificate.coefficient_separation_at n),
    referenceExactCoefficientECompletionCertificate.theta_table_nonempty_at,
    referenceExactCoefficientECompletionCertificate.finite_kloosterman_at,
    referenceExactCoefficientECompletionCertificate.named_boundary_at,
    (fun n => referenceExactCoefficientECompletionCertificate.spectral_decomposition_at n),
    referenceExactCoefficientECompletionCertificate.local_product_one_at,
    referenceExactCoefficientECompletionCertificate.root_allowed_at,
    (fun n => referenceExactCoefficientECompletionCertificate.lvalue_formula_at n)⟩
"""
            text = text[:start] + statement + proof + text[end:]
            changed = True
            print("Mock1Advanced rebuild the exact-coefficient checklist conjunction: applied")

    for name in [
        "referenceMock1DepthOneAbstractVerification",
        "referenceMock1NamedInstance",
    ]:
        old_kw = f"def {name}"
        new_kw = f"noncomputable def {name}"
        if old_kw in text and new_kw not in text:
            text = text.replace(old_kw, new_kw, 1)
            changed = True
            print(f"Mock1Advanced mark {name} noncomputable: applied")

    paper_names = [
        "namedInstanceRegistry", "depthOneConcreteTheoremExtraction",
        "paperObjectFamilySelection", "weightLevelQShiftCuspPrincipalData",
        "t1t5CertificateFields", "sptPrimeGatesAndCrtPortfolio",
        "padicLemmaPortfolio", "rademacherEntropyRegressionInstance",
        "finalConcreteCertificateTheorem", "oneObjectEndToEnd",
    ]
    paper_cases = [f"  | {name} => exact {nested_mem(paper_names[:i+1])}" for i, name in enumerate(paper_names)]
    old = """theorem mem_all (r : PaperInstancesHRequirement) :
    List.Mem r all := by
  cases r <;> simp [all]
"""
    new = "theorem mem_all (r : PaperInstancesHRequirement) :\n    List.Mem r all := by\n  cases r with\n" + "\n".join(paper_cases) + "\n"
    text, did = replace_once(text, old, new,
        "Mock1Advanced prove the paper-instance registry structurally")
    changed |= did

    segment_start = text.find("structure PaperInstancesHCompletionCertificate where")
    segment_end = text.find("end PaperInstancesHCompletionCertificate", segment_start)
    if segment_start >= 0 and segment_end >= 0:
        segment = text[segment_start:segment_end]
        segment2 = segment.replace("  instance : Mock1NamedInstance", "  namedInstance : Mock1NamedInstance")
        segment2 = segment2.replace(" instance.", " namedInstance.")
        segment2 = segment2.replace(" C.instance", " C.namedInstance")
        if segment2 != segment:
            text = text[:segment_start] + segment2 + text[segment_end:]
            changed = True
            print("Mock1Advanced rename the reserved completion-certificate instance field: applied")
    text = text.replace("  instance := referenceMock1NamedInstance\n", "  namedInstance := referenceMock1NamedInstance\n")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_once(text,
        """  simpa only [Nat.cast_mul, Nat.cast_pow, Int.cast_natCast] using h
""",
        """  norm_num only [Int.cast_natCast]
  simpa only [Nat.cast_mul, Nat.cast_pow] using h
""",
        "Mock2 normalize the nested natural-to-integer cast in the modulus proof")
    changed |= did

    text, did = replace_once(text,
        """  simpa only [powerShiftHom] using powerShiftIntegerHom_apply M p k z
""",
        """  change powerShiftIntegerHom M p k z = _
  exact powerShiftIntegerHom_apply M p k z
""",
        "Mock2 expose the lifted integer representative explicitly")
    changed |= did

    text, did = replace_once(text,
        """    simpa only [Nat.cast_mul, Nat.cast_pow] using
      (show (M * p ^ shiftExponent M p k : ZMod (Pk p k)) = 0 from
        (ZMod.natCast_eq_zero_iff _ _).2
          (Pk_dvd_M_mul_shift M p k hM hp))
""",
        """    rw [← Nat.cast_mul]
    exact (ZMod.natCast_eq_zero_iff _ _).2
      (Pk_dvd_M_mul_shift M p k hM hp)
""",
        "Mock2 combine the two natural casts before kernel divisibility")
    changed |= did

    count = text.count("simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow] using")
    if count:
        text = text.replace(
            "simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow] using",
            "norm_num only [Int.cast_natCast] at *\n    simpa only [Int.cast_mul, Nat.cast_pow] using")
        changed = True
        print(f"Mock2 normalize integer-wrapped natural powers: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """        (↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) : ℝ≥0∞) := by
"""
    new = """        ENNReal.ofNNReal ((1 / NNReal.mk z.im z.im_pos.le) ^ 2) := by
"""
    text, changed = replace_once(text, old, new,
        "Mock2Advanced avoid the unsupported ENNReal notation in the density")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
