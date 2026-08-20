from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(text: str, old: str, new: str, expected: int, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == expected:
        print(f"{label}: applied {count}")
        return text.replace(old, new), True
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count == 0:
        raise RuntimeError(f"{label}: source changed; old and new forms absent")
    raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")


def theorem_statement(text: str, namespace: str, theorem: str) -> str:
    ns_start = text.find(f"namespace {namespace}")
    ns_end = text.find(f"end {namespace}", ns_start)
    pos = text.find(f"theorem {theorem}", ns_start, ns_end)
    if min(ns_start, ns_end, pos) < 0:
        raise RuntimeError(f"{namespace}.{theorem}: declaration not found")
    lines = text[pos:].splitlines()
    return_start = None
    for i, line in enumerate(lines[1:], 1):
        if line.rstrip().endswith(") :"):
            return_start = i + 1
            break
    if return_start is None:
        raise RuntimeError(f"{namespace}.{theorem}: return type start absent")
    result: list[str] = []
    for line in lines[return_start:]:
        if ":=" in line:
            before = line.split(":=", 1)[0].rstrip()
            if before:
                result.append(before)
            break
        result.append(line.rstrip())
    while result and not result[0].strip():
        result.pop(0)
    if not result:
        raise RuntimeError(f"{namespace}.{theorem}: empty return type")
    return "\n".join(result)


def requirement_bridge(name: str, requirement_list: str, count: int) -> str:
    lines = [
        f"theorem requirementOf_{name}_at",
        "    (b : AdvancedClaimsIIPromptBullet)",
        f"    (h : List.Mem b {name}Bullets) :",
        "    List.Mem (requirementOf b)",
        f"      AdvancedClaimsIIRequirement.{requirement_list} := by",
        f"  simp only [{name}Bullets] at h",
    ]
    for _ in range(count):
        lines.append("  rcases List.mem_cons.mp h with rfl | h")
        lines.append(
            f"  · simp [requirementOf, AdvancedClaimsIIRequirement.{requirement_list}]"
        )
    lines.append("  cases h")
    return "\n".join(lines)


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    leaf_bridge = """theorem leafStatement_of_ledger
    {C : AdvancedClaimsIICompletionCertificate}
    (L : AdvancedClaimsIIRequirementLeafLedger C)
    (r : AdvancedClaimsIIRequirement) :
    leafStatement C r := by
  cases L
  cases r <;> simp only [leafStatement] <;> assumption

"""
    marker = "end AdvancedClaimsIIRequirement\n\nnamespace AdvancedClaimsIIPromptBullet"
    if "theorem leafStatement_of_ledger" not in text:
        idx = text.find(marker, text.find("def leafStatement"))
        if idx < 0:
            raise RuntimeError("Mock1Advanced leaf ledger insertion marker absent")
        text = text[:idx] + leaf_bridge + text[idx:]
        changed = True
        print("Mock1Advanced restore leafStatement_of_ledger: applied")
    else:
        print("Mock1Advanced restore leafStatement_of_ledger: already applied")

    bridges = "\n\n".join([
        requirement_bridge("objectSchema", "objectSchemaRequirements", 4),
        requirement_bridge("t1t5", "t1t5Requirements", 8),
        requirement_bridge("spt", "sptRequirements", 5),
        requirement_bridge("kernel", "kernelRequirements", 8),
        requirement_bridge("exact", "exactCoefficientRequirements", 7),
        requirement_bridge("pAdic", "pAdicRequirements", 10),
        requirement_bridge("entropy", "entropyReproRequirements", 9),
    ]) + "\n\n"
    if "theorem requirementOf_objectSchema_at" not in text:
        idx = text.find("def groupedBullets", text.find("def objectSchemaBullets"))
        if idx < 0:
            raise RuntimeError("Mock1Advanced grouped-bullet insertion marker absent")
        text = text[:idx] + bridges + text[idx:]
        changed = True
        print("Mock1Advanced restore seven requirementOf group bridges: applied")
    else:
        print("Mock1Advanced restore seven requirementOf group bridges: already applied")

    specs = [
        ("object", "AdvancedClaimsIIActualInputAuditCertificate", "object_schema_actual_inputs_at", "C.actualInputAudit"),
        ("t1t5", "AdvancedClaimsIIActualInputAuditCertificate", "t1t5_actual_inputs_at", "C.actualInputAudit"),
        ("kernel", "AdvancedClaimsIIActualInputAuditCertificate", "kernel_actual_inputs_at", "C.actualInputAudit"),
        ("exact", "AdvancedClaimsIIActualInputAuditCertificate", "exact_actual_inputs_at", "C.actualInputAudit"),
        ("padic", "AdvancedClaimsIIActualInputAuditCertificate", "padic_actual_inputs_at", "C.actualInputAudit"),
        ("entropy", "AdvancedClaimsIIActualInputAuditCertificate", "entropy_actual_inputs_at", "C.actualInputAudit"),
    ]
    alias_defs: list[str] = []
    for short, namespace, theorem, _arg in specs:
        prop = theorem_statement(text, namespace, theorem)
        prop = "\n".join("  " + line.lstrip() for line in prop.splitlines())
        alias_defs.append(
            f"def advancedClaimsII_{short}ActualStatement\n"
            f"    (C : AdvancedClaimsIICompletionCertificate) : Prop :=\n{prop}"
        )
    alias_defs.insert(2,
        """def advancedClaimsII_sptActualValuationStatement
    (C : AdvancedClaimsIICompletionCertificate) : Prop :=
  Nat.Prime C.sptKernel.sptFree.valuation.p /\\
    Dvd.dvd
      (C.sptKernel.sptFree.valuation.p ^ C.sptKernel.sptFree.valuation.vp)
      C.sptKernel.sptFree.valuation.M /\\
    Not (Dvd.dvd
      (C.sptKernel.sptFree.valuation.p ^
        (C.sptKernel.sptFree.valuation.vp + 1))
      C.sptKernel.sptFree.valuation.M)""")
    alias_block = "\n\n".join(alias_defs) + "\n\n"
    if "def advancedClaimsII_objectActualStatement" not in text:
        idx = text.find("structure AdvancedClaimsIISectionConcreteClosureCertificate")
        if idx < 0:
            raise RuntimeError("Mock1Advanced section closure structure absent")
        text = text[:idx] + alias_block + text[idx:]
        changed = True
        print("Mock1Advanced add explicit proposition aliases for audit proofs: applied")
    else:
        print("Mock1Advanced add explicit proposition aliases for audit proofs: already applied")

    field_replacements = [
        ("object_actual", "AdvancedClaimsIIActualInputAuditCertificate.object_schema_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_objectActualStatement C"),
        ("t1t5_actual", "AdvancedClaimsIIActualInputAuditCertificate.t1t5_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_t1t5ActualStatement C"),
        ("spt_actual_valuation", "AdvancedClaimsIIClaimGroupAuditCertificate.spt_actual_valuation_at", "C.claimGroupAudit", "advancedClaimsII_sptActualValuationStatement C"),
        ("kernel_actual", "AdvancedClaimsIIActualInputAuditCertificate.kernel_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_kernelActualStatement C"),
        ("exact_actual", "AdvancedClaimsIIActualInputAuditCertificate.exact_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_exactActualStatement C"),
        ("padic_actual", "AdvancedClaimsIIActualInputAuditCertificate.padic_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_padicActualStatement C"),
        ("entropy_actual", "AdvancedClaimsIIActualInputAuditCertificate.entropy_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_entropyActualStatement C"),
    ]
    struct_start = text.find("structure AdvancedClaimsIISectionConcreteClosureCertificate")
    closure_ns = text.find("namespace AdvancedClaimsIISectionConcreteClosureCertificate", struct_start)
    if min(struct_start, closure_ns) < 0:
        raise RuntimeError("Mock1Advanced section closure region absent")
    struct_region = text[struct_start:closure_ns]
    for field, qualified, arg, alias in field_replacements:
        old = f"  {field} :\n    {qualified}\n      {arg}"
        new = f"  {field} :\n    {alias}"
        struct_region, did = replace_exact(
            struct_region, old, new, 1,
            f"Mock1Advanced type {field} by proposition alias")
        changed |= did
    text = text[:struct_start] + struct_region + text[closure_ns:]

    projection_specs = [
        ("object_actual_at", "AdvancedClaimsIIActualInputAuditCertificate.object_schema_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_objectActualStatement C"),
        ("t1t5_actual_at", "AdvancedClaimsIIActualInputAuditCertificate.t1t5_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_t1t5ActualStatement C"),
        ("spt_actual_valuation_at", "AdvancedClaimsIIClaimGroupAuditCertificate.spt_actual_valuation_at", "C.claimGroupAudit", "advancedClaimsII_sptActualValuationStatement C"),
        ("kernel_actual_at", "AdvancedClaimsIIActualInputAuditCertificate.kernel_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_kernelActualStatement C"),
        ("exact_actual_at", "AdvancedClaimsIIActualInputAuditCertificate.exact_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_exactActualStatement C"),
        ("padic_actual_at", "AdvancedClaimsIIActualInputAuditCertificate.padic_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_padicActualStatement C"),
        ("entropy_actual_at", "AdvancedClaimsIIActualInputAuditCertificate.entropy_actual_inputs_at", "C.actualInputAudit", "advancedClaimsII_entropyActualStatement C"),
    ]
    closure_ns = text.find("namespace AdvancedClaimsIISectionConcreteClosureCertificate")
    for theorem_name, qualified, arg, alias in projection_specs:
        pos = text.find(f"theorem {theorem_name}", closure_ns)
        if pos < 0:
            raise RuntimeError(f"Mock1Advanced projection {theorem_name} absent")
        end = text.find(":=", pos)
        region = text[pos:end]
        old_tail = f":\n    {qualified}\n      {arg} "
        if old_tail in region:
            region = region.replace(old_tail, f":\n    {alias} ", 1)
            text = text[:pos] + region + text[end:]
            changed = True
            print(f"Mock1Advanced projection {theorem_name} explicit proposition: applied")
        elif f":\n    {alias} " in region:
            print(f"Mock1Advanced projection {theorem_name} explicit proposition: already applied")
        else:
            raise RuntimeError(f"Mock1Advanced projection {theorem_name}: source changed")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        ("""  have hz0 : z = 0 := by
    change (M : ℤ) * (z : ℤ) = 0 at hz
    have hMZ : (M : ℤ) ≠ 0 := by exact_mod_cast hM
    exact (mul_eq_zero.mp hz).resolve_left hMZ
""", """  have hz0 : z = 0 := by
    apply integerMul_injective M hM
    simpa only [map_zero] using hz
""", "Mock2 use the proved injectivity of integer multiplication"),
        ("""  change (M : ℤ) • (z • x) = ((M : ℤ) * z) • x
  rw [smul_smul]
""", """  change (M : ℤ) • ((z : ℤ) • x) = ((M : ℤ) * (z : ℤ)) • x
  rw [smul_smul]
""", "Mock2 make tensor-unitor integer scalar coercions explicit"),
        ("""noncomputable def tensorResolutionXTwoIsoZero (M N : ℕ) :
    (tensorResolutionComplex M N).X 2 ≅ (0 : ModuleCat ℤ) := by
""", """noncomputable def tensorResolutionXTwoIsoZero (M N : ℕ) :
    (tensorResolutionComplex M N).X 2 ≅ zeroIntegerModule := by
""", "Mock2 name the zero module instead of numeral notation"),
        ("""      rw [tensorResolutionComplex_d_two_one]
      exact (zero_comp _).symm)
""", """      rw [tensorResolutionComplex_d_two_one]
      simp)
""", "Mock2 close the zero differential square by simplification"),
    ]
    for old, new, label in replacements:
        text, did = replace_exact(text, old, new, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """@[simp]
theorem restrict_apply
"""
    new = """local instance instDecidableMemOpens
    (x : X) (U : TopologicalSpace.Opens X) : Decidable (x ∈ U) :=
  Classical.propDecidable _

@[simp]
theorem restrict_apply
"""
    if "local instance instDecidableMemOpens" in text:
        print("Mock2Advanced install local classical membership decisions before theorem types: already applied")
    else:
        text, did = replace_exact(text, old, new, 1,
            "Mock2Advanced install local classical membership decisions before theorem types")
        changed |= did

    old = """      have hji :
          (s j : X → Fiber) x = (s i : X → Fiber) x := by
        change
          (if x ∈ V j ∧ x ∈ V i then (s j : X → Fiber) x else 0) =
            (if x ∈ V j ∧ x ∈ V i then (s i : X → Fiber) x else 0) at hvalue
        simpa only [hxj, hxi, and_self, if_pos] using hvalue
"""
    new = """      have hji :
          (s j : X → Fiber) x = (s i : X → Fiber) x := by
        simpa [presheaf, restrict_apply, hxj, hxi] using hvalue
"""
    text, did = replace_exact(text, old, new, 1,
        "Mock2Advanced unfold concrete restrictions in the gluing compatibility proof")
    changed |= did

    old = """  rw [← denom_cocycle]
  simpa only [mul_inv, realMatrix_one] using
    (UpperHalfPlane.denom_one τ)
"""
    new = """  rw [← denom_cocycle]
  simpa only [mul_inv_cancel, realMatrix_one] using
    (UpperHalfPlane.denom_one τ)
"""
    text, did = replace_exact(text, old, new, 1,
        "Mock2Advanced simplify the group inverse product with mul_inv_cancel")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2]
  rw [mul_assoc,
    mul_inv_cancel₀ (ModularForm.eta_ne_zero (δ • z).2), mul_one]
"""
    new = """  field_simp [ModularForm.eta_ne_zero z.2,
    ModularForm.eta_ne_zero (δ • z).2,
    ModularForm.eta_ne_zero ((γ * δ) • z).2] <;> ring
"""
    text, did = replace_exact(text, old, new, 1,
        "FunctionalAnalysis normalize the inverse-eta cocycle after clearing denominators")
    changed |= did

    old = """theorem pointwiseInnerDensity_conj_symm
    (m : InvariantFiberMetric M) (u v : WeightSection M) (z : ℍ) :
    star (m.pointwiseInnerDensity v u z) =
      m.pointwiseInnerDensity u v z := by
  simp only [pointwiseInnerDensity, star_mul,
    Complex.conj_ofReal, star_star]
  ring
"""
    new = """theorem pointwiseInnerDensity_conj_symm
    (m : InvariantFiberMetric M) (u v : WeightSection M) (z : ℍ) :
    star (m.pointwiseInnerDensity v u z) =
      m.pointwiseInnerDensity u v z := by
  have hscale : star (m.scale z : ℂ) = (m.scale z : ℂ) := by
    change Complex.conj (m.scale z : ℂ) = (m.scale z : ℂ)
    exact Complex.conj_ofReal (m.scale z)
  simp only [pointwiseInnerDensity, star_mul, star_star, hscale]
  ring
"""
    text, did = replace_exact(text, old, new, 1,
        "FunctionalAnalysis expose conjugation of the real fiber scale")
    changed |= did

    old = """  rw [Complex.conj_mul', Complex.ofReal_mul]

/-- The full cross-density, not only its diagonal, is invariant. -/
"""
    new = """  rw [Complex.conj_mul', Complex.ofReal_mul]
  norm_cast

/-- The full cross-density, not only its diagonal, is invariant. -/
"""
    text, did = replace_exact(text, old, new, 1,
        "FunctionalAnalysis normalize real-to-complex casts in the diagonal density")
    changed |= did

    old = """  have hmetric :
      (m.scale ((γ : SL(2, ℤ)) • z) : ℂ) *
          (star (M.factor γ z) * M.factor γ z) =
        (m.scale z : ℂ) := by
    rw [Complex.conj_mul']
    simpa only [Complex.ofReal_mul] using
      congrArg (fun r : ℝ => (r : ℂ))
        (m.scale_covariance γ z)
  calc
    (m.scale ((γ : SL(2, ℤ)) • z) : ℂ) *
          (star (M.factor γ z) * star (u z)) *
          (M.factor γ z * v z) =
"""
    new = """  have hmetric :
      (m.scale ((γ : SL(2, ℤ)) • z) : ℂ) *
          (star (M.factor γ z) * M.factor γ z) =
        (m.scale z : ℂ) := by
    change (m.scale ((γ : SL(2, ℤ)) • z) : ℂ) *
        ((starRingEnd ℂ) (M.factor γ z) * M.factor γ z) =
      (m.scale z : ℂ)
    rw [Complex.conj_mul']
    simpa only [Complex.ofReal_mul] using
      congrArg (fun r : ℝ => (r : ℂ))
        (m.scale_covariance γ z)
  calc
    (m.scale ((γ : SL(2, ℤ)) • z) : ℂ) *
          (star (u z) * star (M.factor γ z)) *
          (M.factor γ z * v z) =
"""
    text, did = replace_exact(text, old, new, 1,
        "FunctionalAnalysis align conjugation order and the complex norm identity")
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
