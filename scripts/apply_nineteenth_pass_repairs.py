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


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    text, did = replace_once(
        text,
        """open Filter Topology

structure Mock1AdvancedCompatibilityCertificate where
""",
        """open Filter Topology

universe uHol uShadow

structure Mock1AdvancedCompatibilityCertificate where
""",
        "Mock1Advanced name the compatibility universes")
    changed |= did

    old_fields = """  corollary1_holomorphic :
    forall {X : Type*} (Fminus R : X -> Complex) (S : Complex),
      (forall x, Fminus x = (Complex.I / 2) * S * R x) ->
        S = 0 ->
          forall x, Fminus x = 0
  shadow_zero :
    forall {X : Type*} (xiFhat g : X -> Complex) (S kappa : Complex),
      (forall x, xiFhat x = S * kappa * g x) ->
        S = 0 ->
          forall x, xiFhat x = 0
"""
    new_fields = """  corollary1_holomorphic :
    forall {X : Type uHol} (Fminus R : X -> Complex) (S : Complex),
      (forall x, Fminus x = (Complex.I / 2) * S * R x) ->
        S = 0 ->
          forall x, Fminus x = 0
  shadow_zero :
    forall {X : Type uShadow} (xiFhat g : X -> Complex) (S kappa : Complex),
      (forall x, xiFhat x = S * kappa * g x) ->
        S = 0 ->
          forall x, xiFhat x = 0
"""
    text, did = replace_once(text, old_fields, new_fields,
        "Mock1Advanced preserve separate theorem universes explicitly")
    changed |= did

    start = text.find("namespace Mock1AdvancedCompatibilityCertificate")
    end = text.find("end Mock1AdvancedCompatibilityCertificate", start)
    if start >= 0 and end >= 0:
        region = text[start:end]
        region2 = region.replace(
            "(C : Mock1AdvancedCompatibilityCertificate)",
            "(C : Mock1AdvancedCompatibilityCertificate.{uHol, uShadow})")
        region2 = region2.replace(
            "{X : Type*} (Fminus R : X -> Complex)",
            "{X : Type uHol} (Fminus R : X -> Complex)")
        region2 = region2.replace(
            "{X : Type*} (xiFhat g : X -> Complex)",
            "{X : Type uShadow} (xiFhat g : X -> Complex)")
        old_body = """  C.corollary1_holomorphic (X := X) Fminus R S hsplit hS
"""
        new_body = """  Mock1Adv.corollary1_holomorphic Fminus R S hsplit hS
"""
        region2 = region2.replace(old_body, new_body)
        old_body = """  C.shadow_zero (X := X) xiFhat g S kappa hshadow hS
"""
        new_body = """  Mock1Adv.shadow_zero_of_S_zero xiFhat g S kappa hshadow hS
"""
        region2 = region2.replace(old_body, new_body)
        if region2 != region:
            text = text[:start] + region2 + text[end:]
            changed = True
            print("Mock1Advanced align compatibility method universes: applied")
    else:
        print("Mock1Advanced compatibility namespace anchors missing")

    exact_replacements = [
        ("""def referenceMock1AdvancedCompatibilityCertificate :
    Mock1AdvancedCompatibilityCertificate where
""",
         """def referenceMock1AdvancedCompatibilityCertificate :
    Mock1AdvancedCompatibilityCertificate.{0, 0} where
""",
         "Mock1Advanced fix reference certificate universe instance"),
        ("""noncomputable def reference_mock1_advanced_compatibility :
    Mock1AdvancedCompatibilityCertificate :=
""",
         """noncomputable def reference_mock1_advanced_compatibility :
    Mock1AdvancedCompatibilityCertificate.{0, 0} :=
""",
         "Mock1Advanced fix compatibility alias universe instance"),
        ("""  referenceMock1AdvancedCompatibilityCertificate.corollary1_holomorphic_at
    (X := X) Fminus R S hsplit hS
""",
         """  Mock1Adv.corollary1_holomorphic Fminus R S hsplit hS
""",
         "Mock1Advanced retain generic reference corollary theorem"),
        ("""  referenceMock1AdvancedCompatibilityCertificate.shadow_zero_at
    (X := X) xiFhat g S kappa hshadow hS
""",
         """  Mock1Adv.shadow_zero_of_S_zero xiFhat g S kappa hshadow hS
""",
         "Mock1Advanced retain generic reference shadow theorem"),
        ("  mock1Compatibility : Mock1AdvancedCompatibilityCertificate\n",
         "  mock1Compatibility : Mock1AdvancedCompatibilityCertificate.{0, 0}\n",
         "Mock1Advanced fix release compatibility universe instance"),
        ("""theorem mock1_compatibility_at
    (R : UnconditionalCertificationReleaseEnvelope) :
    Mock1AdvancedCompatibilityCertificate :=
""",
         """theorem mock1_compatibility_at
    (R : UnconditionalCertificationReleaseEnvelope) :
    Mock1AdvancedCompatibilityCertificate.{0, 0} :=
""",
         "Mock1Advanced fix release compatibility accessor universe"),
        ("""theorem reference_release_mock1_compatibility :
    Mock1AdvancedCompatibilityCertificate :=
""",
         """theorem reference_release_mock1_compatibility :
    Mock1AdvancedCompatibilityCertificate.{0, 0} :=
""",
         "Mock1Advanced fix reference release compatibility universe"),
    ]
    for old, new, label in exact_replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        ("""  comm₁₂ := by simp
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
""",
         """  comm₁₂ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
""",
         "Mock2 prove left zero square from the trivial source"),
        ("""  comm₂₃ := by simp

/-- Naturality morphism for the short complex ending in the literal cokernel. -/
""",
         """  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact Subsingleton.elim _ _

/-- Naturality morphism for the short complex ending in the literal cokernel. -/
""",
         "Mock2 prove gcd-to-zero square in the trivial target"),
        ("""  comm₂₃ := by simp

/-- Auditable statement of the proven naturality range. -/
""",
         """  comm₂₃ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact Subsingleton.elim _ _

/-- Auditable statement of the proven naturality range. -/
""",
         "Mock2 prove cokernel-to-zero square in the trivial target"),
    ]
    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    old = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ((↑(1 / (⟨z.im, z.im_pos.le⟩ : NNReal)) : ENNReal) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    new = """theorem hyperbolicMeasure_def :
    hyperbolicMeasure =
      (volume.comap UpperHalfPlane.coe).withDensity fun z =>
        ((1 / (↑(⟨z.im, z.im_pos.le⟩ : NNReal) : ENNReal)) ^ 2) := by
  simpa only [hyperbolicMeasure] using UpperHalfPlane.volume_def
"""
    text, changed = replace_once(text, old, new,
        "Mock2Advanced cast the hyperbolic denominator before inversion")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """set_option maxHeartbeats 800000 in
noncomputable def realifiedFunctionalLinear (F : StrongAntiDual V) : V →ₗ[ℝ] ℝ where
  toFun v := (F v).re
  map_add' u v := by
    simp
  map_smul' r v := by
    have hr : r • v = (r : ℂ) • v := rfl
    simp only [hr, map_smulₛₗ, starRingEnd_apply, Complex.star_def,
      Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul]
"""
    new = """noncomputable def realifiedFunctionalLinear (F : StrongAntiDual V) : V →ₗ[ℝ] ℝ := by
  set_option maxHeartbeats 800000 maxRecDepth 10000 in
    exact
      { toFun := fun v => (F v).re
        map_add' := by
          intro u v
          simp
        map_smul' := by
          intro r v
          have hr : r • v = (r : ℂ) • v := rfl
          simp only [hr, map_smulₛₗ, starRingEnd_apply, Complex.star_def,
            Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul] }
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis move functional realification options into the RHS")
    changed |= did

    old = """set_option maxHeartbeats 800000 in
noncomputable def realifiedFormLinear (B : ContinuousSesquilinearForm V) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => (B u v).re)
    (by
      intro u₁ u₂ v
      simp)
    (by
      intro r u v
      have hr : r • u = (r : ℂ) • u := rfl
      simp only [hr, map_smul, ContinuousLinearMap.smul_apply,
        smul_eq_mul, Complex.re_ofReal_mul])
    (by
      intro u v₁ v₂
      simp)
    (by
      intro r u v
      have hr : r • v = (r : ℂ) • v := rfl
      simp only [hr, map_smulₛₗ, starRingEnd_apply, Complex.star_def,
        Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul])
"""
    new = """noncomputable def realifiedFormLinear (B : ContinuousSesquilinearForm V) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ := by
  set_option maxHeartbeats 800000 maxRecDepth 10000 in
    exact LinearMap.mk₂ ℝ (fun u v => (B u v).re)
      (by
        intro u₁ u₂ v
        simp)
      (by
        intro r u v
        have hr : r • u = (r : ℂ) • u := rfl
        simp only [hr, map_smul, smul_apply,
          smul_eq_mul, Complex.re_ofReal_mul])
      (by
        intro u v₁ v₂
        simp)
      (by
        intro r u v
        have hr : r • v = (r : ℂ) • v := rfl
        simp only [hr, map_smulₛₗ, starRingEnd_apply, Complex.star_def,
          Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul])
"""
    text, did = replace_once(text, old, new,
        "FunctionalAnalysis move form realification options into the RHS")
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
