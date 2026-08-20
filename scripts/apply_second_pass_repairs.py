from __future__ import annotations

import re
from pathlib import Path

from apply_spt2_cotangent_final import main as repair_spt2_cotangent_final

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


def repair_spt4() -> None:
    path = ROOT / "Spt4.lean"
    text = path.read_text(encoding="utf-8")
    marker = "theorem resC_d_succ_zero (N j : ℕ)"
    if "set_option maxHeartbeats 800000 in\n" + marker in text:
        print("Spt4 local heartbeat: already applied")
        return
    if marker not in text:
        print("Spt4 local heartbeat: source changed")
        return
    text = text.replace(marker, "set_option maxHeartbeats 800000 in\n" + marker, 1)
    path.write_text(text, encoding="utf-8", newline="\n")
    print("Spt4 local heartbeat: applied")


def repair_mock1() -> None:
    path = ROOT / "Mock1.lean"
    changed = False
    changed |= replace_once(path,
"""  rw [zsmul_eq_mul]
  change ((Nat.gcd M N : ZMod N) *
""",
"""  rw [zsmul_eq_mul, Int.cast_natCast]
  change ((Nat.gcd M N : ZMod N) *
""", "Mock1 normalize the integer cast of gcd")
    changed |= replace_once(path,
"""  apply Subtype.ext
  simp [zmodGcdToTorProxyHom, torProxyGeneratorIntHom]
""",
"""  change (1 : ℤ) • torProxyExplicitGenerator M N = torProxyExplicitGenerator M N
  simp
""", "Mock1 evaluate the ZMod lift at one")
    changed |= replace_once(path,
"""      have hx : (M : ZMod N') * ((x : TorProxy M N') : ZMod N') = 0 := by
        simpa using x.property
      have hmap := congrArg (fun y : ZMod N' => (ZMod.castHom h (ZMod N)) y) hx
      simpa using hmap⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
""",
"""      have hx : (M : ZMod N') * ((x : TorProxy M N') : ZMod N') = 0 := by
        change (M : ZMod N') * (x : ZMod N') = 0
        exact x.property
      have hmap := congrArg (fun y : ZMod N' => (ZMod.castHom h (ZMod N)) y) hx
      simpa only [map_mul, map_natCast, map_zero] using hmap⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (ZMod.castHom h (ZMod N))
  map_add' x y := by
    apply Subtype.ext
    exact map_add (ZMod.castHom h (ZMod N)) (x : ZMod N') (y : ZMod N')
""", "Mock1 make level reduction functorial explicitly")
    changed |= replace_once(path,
"""      (ZMod.castHom h (ZMod N))
        ((M : ZMod N') * ((x : TorProxy M N') : ZMod N')) := by
  simp [torProxyLevelReduction_coe]
""",
"""      (ZMod.castHom h (ZMod N))
        ((M : ZMod N') * ((x : TorProxy M N') : ZMod N')) := by
  simp only [torProxyLevelReduction_coe, map_mul, map_natCast]
""", "Mock1 level reduction commutes with multiplication")
    print("Mock1 second-wave changed source." if changed else "No Mock1 second-wave changes.")


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False
    old = """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  classical
  cases key <;> simp [all]
"""
    new = """theorem mem_all (key : RequirementKey) :
    List.Mem key all := by
  cases key <;> decide
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True
        print("Mock1Advanced finite requirement audit: applied")
    text2, n = re.subn(
        r"(theorem coverage_targets_[A-Za-z0-9_']+\s*:[\s\S]*?\s*:= by)\n  classical\n  simp \[targets\]",
        r"\1\n  decide",
        text,
    )
    if n:
        text = text2; changed = True
        print(f"Mock1Advanced concrete target audits: applied {n}")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False
    duplicate = "include hM hp in\ninclude hM hp in\n"
    if duplicate in text:
        text = text.replace(duplicate, "include hM hp in\n", 1); changed = True
        print("Mock2 duplicate include: removed")
    old = """  by_cases hq : q = p
  · subst q
    simp [Pk_factorization_self p k hp]
  · simp [hq, Pk_factorization_ne p k hp hq]
"""
    new = """  by_cases hq : q = p
  · subst q
    rw [if_pos rfl]
    exact Pk_factorization_self p k hp
  · rw [if_neg hq]
    exact Pk_factorization_ne p k hp hq
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True
        print("Mock2 prime-power pointwise factorization: applied")
    old = """  by_cases hq : q = p
  · subst q
    simp [gcd_M_Pk_factorization_self M p k hM hp]
  · simp [hq, gcd_M_Pk_factorization_ne M p k hM hp hq]
"""
    new = """  by_cases hq : q = p
  · subst q
    rw [if_pos rfl]
    exact gcd_M_Pk_factorization_self M p k hM hp
  · rw [if_neg hq]
    exact gcd_M_Pk_factorization_ne M p k hM hp hq
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True
        print("Mock2 gcd pointwise factorization: applied")
    anchor = """/-- Full valuation-free factorization of `gcd(M,p^k)`.  This is stronger than
"""
    if anchor in text and "include hM hp in\n" + anchor not in text:
        text = text.replace(anchor, "include hM hp in\n" + anchor, 1); changed = True
        print("Mock2 full gcd factorization scope: restored")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False
    old = """/-- The inner product supplies the canonical anti-dual pairing in the test
variable, with exactly the orientation used by `∫ g * conj v`.
-/
omit [NormedSpace ℂ E] in
"""
    new = """/- The inner product supplies the canonical anti-dual pairing in the test
variable, with exactly the orientation used by `∫ g * conj v`.
-/
omit [NormedSpace ℂ E] in
"""
    if old in text:
        text = text.replace(old, new, 1); changed = True
        print("FunctionalAnalysis omit command placement: repaired")
    text2, n = re.subn(r"(?m)^def shiftedForm\b", "noncomputable def shiftedForm", text, count=1)
    if n: text, changed = text2, True
    text2, n = re.subn(r"(?m)^def rieszShiftedForm\b", "noncomputable def rieszShiftedForm", text, count=1)
    if n: text, changed = text2, True
    old = "exact (mul_le_mul_right hnorm).1 hcancel"
    if old in text:
        text = text.replace(old, "exact le_of_mul_le_mul_right hcancel hnorm.le", 1)
        changed = True
        print("FunctionalAnalysis positive-factor cancellation: repaired")
    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_spt2_cotangent_final()
    repair_spt4()
    repair_mock1()
    repair_mock1_advanced()
    repair_mock2()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
