from __future__ import annotations

import re
from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(path: Path, old: str, new: str, label: str) -> bool:
    text = path.read_text(encoding="utf-8")
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied/source changed")
        return False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    path.write_text(text.replace(old, new), encoding="utf-8", newline="\n")
    print(f"{label}: applied")
    return True


def repair_mock1() -> None:
    path = ROOT / "Mock1.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem zmodGcdToTorProxyHom_one (M N : ℕ) [NeZero N] :
    zmodGcdToTorProxyHom M N 1 = torProxyExplicitGenerator M N := by
  change (1 : ℤ) • torProxyExplicitGenerator M N = torProxyExplicitGenerator M N
  simp
"""
    new = """theorem zmodGcdToTorProxyHom_one (M N : ℕ) [NeZero N] :
    zmodGcdToTorProxyHom M N 1 = torProxyExplicitGenerator M N := by
  unfold zmodGcdToTorProxyHom
  rw [← Int.cast_one, ZMod.lift_coe]
  rfl
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True
        print("Mock1 evaluate ZMod lift at one: applied")

    old = """      have hmap := congrArg (fun y : ZMod N' => (ZMod.castHom h (ZMod N)) y) hx
      simpa only [map_mul, map_natCast, map_zero] using hmap⟩
"""
    new = """      have hmap := congrArg (fun y : ZMod N' => (ZMod.castHom h (ZMod N)) y) hx
      change (M : ZMod N) *
        (ZMod.castHom h (ZMod N)) ((x : TorProxy M N') : ZMod N') = 0
      simpa only [map_mul, map_natCast, map_zero] using hmap⟩
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True
        print("Mock1 expose level-reduction kernel membership: applied")

    if "(ZMod.equivPi hg).toAddEquiv" in text:
        text = text.replace("(ZMod.equivPi hg).toAddEquiv",
            "(ZMod.equivPi (Nat.gcd M N) hg).toAddEquiv", 1)
        changed = True
        print("Mock1 pass modulus to ZMod.equivPi: applied")

    old_expr = "gcdToPrimewise ((torProxy_equiv_zmod_gcd M N) x)"
    new_expr = """gcdToPrimewise
          ((ZMod.ringEquivCongr (Nat.gcd_comm N M))
            ((torProxy_equiv_zmod_gcd M N) x))"""
    count = text.count(old_expr)
    if count:
        text = text.replace(old_expr, new_expr)
        changed = True
        print(f"Mock1 orient gcd CRT input: applied {count}")

    old_expr = "C.gcdToPrimewise ((torProxy_equiv_zmod_gcd M N) x)"
    new_expr = """C.gcdToPrimewise
        ((ZMod.ringEquivCongr (Nat.gcd_comm N M))
          ((torProxy_equiv_zmod_gcd M N) x))"""
    count = text.count(old_expr)
    if count:
        text = text.replace(old_expr, new_expr)
        changed = True
        print(f"Mock1 orient certificate gcd CRT input: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  cases key <;> decide
"""
    new = """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  classical
  cases key <;> simp [all]
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True
        print("Mock1Advanced requirement membership by simplification: applied")

    text2, n = re.subn(
        r"(theorem coverage_targets_[A-Za-z0-9_']+\s*:[\s\S]*?\s*:= by)\n  decide",
        r"\1\n  classical\n  simp [targets]",
        text,
    )
    if n:
        text = text2; changed = True
        print(f"Mock1Advanced coverage target membership: applied {n}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    pairs = [
      ("""theorem Phi_comp_intersectionIdealIncl_eq_zero (M N : ℕ) :
    (Phi M N).comp (intersectionIdealIncl M N) = 0 := by
  ext x
  exact Phi_intersectionIdealIncl_eq_zero M N x
""",
       """theorem Phi_comp_intersectionIdealIncl_eq_zero (M N : ℕ) :
    (Phi M N).comp (intersectionIdealIncl M N) = 0 := by
  apply AddMonoidHom.ext
  intro x
  exact Phi_intersectionIdealIncl_eq_zero M N x
""", "literal intersection composite extensionality"),
      ("""  map_add' x y := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
""",
       """  map_add' x y := by
    change
      (ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N))) (x.1 + y.1) -
          (ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N))) (x.2 + y.2) =
        ((ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N))) x.1 -
            (ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N))) x.2) +
          ((ZMod.castHom (Nat.gcd_dvd_left M N) (ZMod (Nat.gcd M N))) y.1 -
            (ZMod.castHom (Nat.gcd_dvd_right M N) (ZMod (Nat.gcd M N))) y.2)
    rw [map_add, map_add]
    abel
""", "psi additivity"),
      ("""@[simp] theorem psi_representatives_apply (M N : ℕ) (a b : ℤ) :
    psi M N ((a : ZMod M), (b : ZMod N)) =
      ((a - b : ℤ) : ZMod (Nat.gcd M N)) := by
  simp [psi, sub_eq_add_neg]
""",
       """@[simp] theorem psi_representatives_apply (M N : ℕ) (a b : ℤ) :
    psi M N ((a : ZMod M), (b : ZMod N)) =
      ((a - b : ℤ) : ZMod (Nat.gcd M N)) := by
  simp only [psi_apply, map_intCast, Int.cast_sub]
""", "psi representative formula"),
      ("""theorem psi_Phi_eq_zero (M N : ℕ) (z : ℤ) :
    psi M N (Phi M N z) = 0 := by
  simp [Phi, psi]
""",
       """theorem psi_Phi_eq_zero (M N : ℕ) (z : ℤ) :
    psi M N (Phi M N z) = 0 := by
  rw [Phi_apply, psi_representatives_apply]
  simp
""", "psi after Phi"),
      ("""theorem psi_comp_Phi_eq_zero (M N : ℕ) :
    (psi M N).comp (Phi M N) = 0 := by
  ext z
  exact psi_Phi_eq_zero M N z
""",
       """theorem psi_comp_Phi_eq_zero (M N : ℕ) :
    (psi M N).comp (Phi M N) = 0 := by
  apply AddMonoidHom.ext
  intro z
  exact psi_Phi_eq_zero M N z
""", "psi-Phi composite extensionality"),
      ("""  · intro hz
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hz
    simpa [PhiKernelModel] using x.property
""",
       """  · intro hz
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hz
    change (PhiKernelIncl M N x : ℤ) ∈
      AddSubgroup.zmultiples (lcm (M : ℤ) (N : ℤ))
    exact x.property
""", "Phi kernel inclusion membership"),
      ("""theorem Phi_comp_PhiKernelIncl_eq_zero (M N : ℕ) :
    (Phi M N).comp (PhiKernelIncl M N) = 0 := by
  ext x
  exact Phi_PhiKernelIncl_eq_zero M N x
""",
       """theorem Phi_comp_PhiKernelIncl_eq_zero (M N : ℕ) :
    (Phi M N).comp (PhiKernelIncl M N) = 0 := by
  apply AddMonoidHom.ext
  intro x
  exact Phi_PhiKernelIncl_eq_zero M N x
""", "kernel-model composite extensionality")]

    for old, new, label in pairs:
        if old in text:
            text = text.replace(old, new, 1); changed = True
            print(f"Mock2 {label}: applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    if "omit [NormedSpace ℂ E] in\ntheorem innerSLFlip_pairing" in text:
        text = text.replace("omit [NormedSpace ℂ E] in\ntheorem innerSLFlip_pairing",
                            "theorem innerSLFlip_pairing", 1)
        changed = True
        print("FunctionalAnalysis reuse ambient NormedSpace instance: applied")

    for marker in [
        "noncomputable def realifiedFunctionalLinear",
        "noncomputable def realifiedFormLinear",
        "theorem weakAntiEquation_of_forall_re_eq",
    ]:
        option_marker = "set_option maxRecDepth 2000 in\n" + marker
        if marker in text and option_marker not in text:
            text = text.replace(marker, option_marker, 1)
            changed = True
            print(f"FunctionalAnalysis local recursion budget for {marker.split()[-1]}: applied")

    if "exact le_of_mul_le_mul_right hcancel hnorm.le" in text:
        text = text.replace("exact le_of_mul_le_mul_right hcancel hnorm.le",
                            "exact le_of_mul_le_mul_right hcancel hnorm", 1)
        changed = True
        print("FunctionalAnalysis positive-factor cancellation: applied")

    old = """    have hv := congrArg (fun G : StrongAntiDual V => G v) hshift
    simpa only [shiftedForm_apply] using hv
"""
    new = """    have hv := congrArg (fun G : StrongAntiDual V => G v) hshift
    change (B u) v + (lam : ℂ) * (mass u) v = F v
    exact hv
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True
        print("FunctionalAnalysis expose shifted-form application: applied")

    count = text.count("𝓝")
    if count:
        text = text.replace("𝓝", "nhds")
        changed = True
        print(f"FunctionalAnalysis replace unavailable nhds notation: applied {count}")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1()
    repair_mock1_advanced()
    repair_mock2()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
