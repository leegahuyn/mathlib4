from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1.lean")

CLOSED_DECIDE = {
    "pdfMahler_value_3", "pdfMahler_value_4", "pdfMahler_value_5",
    "pdfMahler_finiteEval_value_0", "pdfMahler_finiteEval_value_1",
    "pdfMahler_finiteEval_value_2", "pdfMahler_finiteEval_value_3",
    "pdfMahler_finiteEval_value_4", "pdfMahler_finiteEval_value_5",
    "pdfMahler_extrapolated_6", "pdfMahler_extrapolated_7",
    "pdfMahler_extrapolated_8", "pdfMahler_extrapolated_9",
    "pdfMahler_extrapolated_10",
}


def replace_closed_proof(lines: list[str], name: str) -> bool:
    starts = [i for i, line in enumerate(lines) if line.startswith(f"theorem {name}")]
    if not starts:
        print(f"Mock1 {name}: source changed")
        return False
    if len(starts) != 1:
        raise RuntimeError(f"Mock1 {name}: expected one declaration, found {len(starts)}")
    start = starts[0]
    end = start + 1
    while end < len(lines) and lines[end].strip():
        end += 1
    block = lines[start:end]
    proof_index = next((i for i, line in enumerate(block) if ":= by" in line), None)
    if proof_index is None:
        print(f"Mock1 {name}: already converted/source changed")
        return False
    proof_tail = block[proof_index + 1:]
    if not proof_tail or len(proof_tail) > 4 or not any("norm_num" in line for line in proof_tail):
        print(f"Mock1 {name}: proof shape not eligible")
        return False
    lines[start:end] = block[:proof_index + 1] + ["  decide"]
    print(f"Mock1 {name}: closed by kernel decision")
    return True


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied/source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def main() -> int:
    lines = PATH.read_text(encoding="utf-8").splitlines()
    changed = False
    for name in CLOSED_DECIDE:
        changed |= replace_closed_proof(lines, name)
    text = "\n".join(lines) + "\n"

    old = """    constructor
    · intro n
      exact (lcm_dvd_iff.mp
        ((lcmIdealCondition_iff_dvd M pk (x n - y n)).mp (h n))).1
    · intro n
      exact (lcm_dvd_iff.mp
        ((lcmIdealCondition_iff_dvd M pk (x n - y n)).mp (h n))).2
  · intro h n
    exact (lcmIdealCondition_iff_dvd M pk (x n - y n)).mpr
      (lcm_dvd_iff.mpr ⟨h.1 n, h.2 n⟩)
"""
    new = """    constructor
    · intro n
      exact (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left M pk)).trans
        ((lcmIdealCondition_iff_dvd M pk (x n - y n)).mp (h n))
    · intro n
      exact (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right M pk)).trans
        ((lcmIdealCondition_iff_dvd M pk (x n - y n)).mp (h n))
  · intro h n
    exact (lcmIdealCondition_iff_dvd M pk (x n - y n)).mpr
      (Int.natCast_dvd_natCast.mpr
        (Nat.lcm_dvd (Int.natCast_dvd_natCast.mp (h.1 n))
          (Int.natCast_dvd_natCast.mp (h.2 n))))
"""
    text, did = replace_once(text, old, new,
        "Mock1 split Nat.lcm divisibility after integer cast")
    changed |= did

    old = """  have hzDvd : (pk : ℤ) ∣ z :=
    (lcm_dvd_iff.mp ((lcmIdealCondition_iff_dvd M pk z).mp hzLcm)).2
"""
    new = """  have hzDvd : (pk : ℤ) ∣ z :=
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right M pk)).trans
      ((lcmIdealCondition_iff_dvd M pk z).mp hzLcm)
"""
    text, did = replace_once(text, old, new,
        "Mock1 extract right divisor from Nat.lcm cast")
    changed |= did

    old = """  exact (vector_glueable_iff_forall_gcd_dvd (M : ℤ) (N : ℤ) D left right).mpr
    (fun i =>
      (Int.gcd_dvd_left (M : ℤ) (N : ℤ)).trans
        ((lcm_dvd_iff.mp
          ((lcmIdealCondition_iff_dvd M N (left i - right i)).mp (hoverlap i))).1))
"""
    new = """  exact (vector_glueable_iff_forall_gcd_dvd (M : ℤ) (N : ℤ) D left right).mpr
    (fun i =>
      (Int.gcd_dvd_left (M : ℤ) (N : ℤ)).trans
        ((Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left M N)).trans
          ((lcmIdealCondition_iff_dvd M N (left i - right i)).mp (hoverlap i))))
"""
    text, did = replace_once(text, old, new,
        "Mock1 build D4 gate from cast Nat.lcm divisibility")
    changed |= did

    old = """  have hfree : Subsingleton (TorProxy M N) ↔ Nat.Coprime M N := by
    rw [torProxy_subsingleton_iff_gcd_eq_one M N, Nat.gcd_comm N M]
    exact obstructionFree_iff_coprime M N
"""
    new = """  have hfree : Subsingleton (TorProxy M N) ↔ Nat.Coprime M N := by
    rw [torProxy_subsingleton_iff_gcd_eq_one M N, Nat.gcd_comm N M]
"""
    text, did = replace_once(text, old, new,
        "Mock1 remove proof command after rewrite closes obstruction goal")
    changed |= did

    old = """theorem principalPart_eq_principalPartSum
    (C : BlockFamilyCertificate D I Completion Shadow) :
    C.assembledPrincipalPart = C.principalPartSum := by
  simpa [principalPartSum] using C.principalPart_linear
"""
    new = """theorem principalPart_eq_principalPartSum
    (C : BlockFamilyCertificate D I Completion Shadow) :
    C.assembledPrincipalPart = C.principalPartSum := by
  exact C.principalPart_linear
"""
    text, did = replace_once(text, old, new,
        "Mock1 use definitionally identical principal-part sum")
    changed |= did

    old = """@[simp] theorem S4ActualExtractionMatrix_left_apply (i j : Fin S4D) :
    S4ActualExtractionMatrix i (Sum.inl j) =
      if i = j then (1 : ℚ) else 0 := by
  simp [S4ActualExtractionMatrix, s4ActualExtractionEntry, s4ColumnIndex,
    s4ColumnIsHalfResidue, S4PhaseSign]
"""
    new = """@[simp] theorem S4ActualExtractionMatrix_left_apply (i j : Fin S4D) :
    S4ActualExtractionMatrix i (Sum.inl j) =
      if i = j then (1 : ℚ) else 0 := by
  rfl
"""
    text, did = replace_once(text, old, new,
        "Mock1 compute left extraction entry definitionally")
    changed |= did

    old = """@[simp] theorem S4ActualExtractionMatrix_right_apply (i j : Fin S4D) :
    S4ActualExtractionMatrix i (Sum.inr j) =
      if i = j then (-1 : ℚ) else 0 := by
  simp [S4ActualExtractionMatrix, s4ActualExtractionEntry, s4ColumnIndex,
    s4ColumnIsHalfResidue, S4PhaseSign]
"""
    new = """@[simp] theorem S4ActualExtractionMatrix_right_apply (i j : Fin S4D) :
    S4ActualExtractionMatrix i (Sum.inr j) =
      if i = j then (-1 : ℚ) else 0 := by
  rfl
"""
    text, did = replace_once(text, old, new,
        "Mock1 compute right extraction entry definitionally")
    changed |= did

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
