from __future__ import annotations

import re
from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock1.lean")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        print(f"{label}: already applied or source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    text2, count = re.subn(
        r"List\.mem_map_of_mem\s+[A-Za-z_][A-Za-z0-9_'.]*\s+\(",
        "List.mem_map_of_mem (",
        text,
    )
    if count:
        print(f"Mock1 List.mem_map_of_mem API: applied {count} replacements")
        text, changed = text2, True

    text, c = replace_once(
        text,
        """theorem paperClaimInventory_ids_match_claim_universe :
    PaperClaimInventory.map (fun e => e.id) = PaperClaimId.all := by
  unfold PaperClaimInventory
  simp
""",
        """theorem paperClaimInventory_ids_match_claim_universe :
    PaperClaimInventory.map (fun e => e.id) = PaperClaimId.all := by
  unfold PaperClaimInventory
  simp [List.map_map, Function.comp_def]
""",
        "Mock1 inventory ids",
    )
    changed |= c

    text, c = replace_once(
        text,
        """  rcases List.mem_map.mp he with ⟨id, _hid, rfl⟩
  exact paperClaimInventoryEntry_status id
""",
        """  rcases List.mem_map.mp he with ⟨id, _hid, rfl⟩
  simpa [paperClaimInventoryEntry_id] using paperClaimInventoryEntry_status id
""",
        "Mock1 inventory status",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem paperClaimInventory_external_human_audit_note_nonempty :
""",
        """set_option maxRecDepth 10000 in
theorem paperClaimInventory_external_human_audit_note_nonempty :
""",
        "Mock1 local recursion depth",
    )
    changed |= c

    text, c = replace_once(
        text,
        """def TorProxy (M N : ℕ) [NeZero N] : Type :=
  (AddMonoidHom.mulLeft (M : ZMod N)).ker

/-- The carrier subgroup underlying `TorProxy`. -/
""",
        """def TorProxy (M N : ℕ) [NeZero N] : Type :=
  (AddMonoidHom.mulLeft (M : ZMod N)).ker

instance torProxyCoe (M N : ℕ) [NeZero N] : Coe (TorProxy M N) (ZMod N) where
  coe x := x.1

@[ext] theorem torProxy_ext {M N : ℕ} [NeZero N] {x y : TorProxy M N}
    (h : (x : ZMod N) = (y : ZMod N)) : x = y := by
  apply Subtype.ext
  exact h

/-- The carrier subgroup underlying `TorProxy`. -/
""",
        "Mock1 TorProxy coercion and extensionality",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem torProxy_generator_dvd (M N : ℕ) :
    N ∣ M * (N / Nat.gcd M N) := by
  let g := Nat.gcd M N
  have hM : M = g * (M / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left M N)).symm
  have hN : N = g * (N / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right M N)).symm
  refine ⟨M / g, ?_⟩
  calc
    M * (N / g) = (g * (M / g)) * (N / g) := by rw [hM]
    _ = (g * (N / g)) * (M / g) := by ac_rfl
    _ = N * (M / g) := by rw [← hN]
""",
        """theorem torProxy_generator_dvd (M N : ℕ) :
    N ∣ M * (N / Nat.gcd M N) := by
  let g := Nat.gcd M N
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_left M N
  refine ⟨c, ?_⟩
  calc
    M * (N / g) = (g * c) * (N / g) := by rw [hc]
    _ = (g * (N / g)) * c := by ac_rfl
    _ = N * c := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right M N)]
""",
        "Mock1 Tor generator divisibility",
    )
    changed |= c

    text, c = replace_once(
        text,
        """theorem zmodGcdToTorProxyHom_one (M N : ℕ) [NeZero N] :
    zmodGcdToTorProxyHom M N 1 = torProxyExplicitGenerator M N := by
  simp [zmodGcdToTorProxyHom, torProxyGeneratorIntHom]
""",
        """theorem zmodGcdToTorProxyHom_one (M N : ℕ) [NeZero N] :
    zmodGcdToTorProxyHom M N 1 = torProxyExplicitGenerator M N := by
  apply torProxy_ext
  simp [zmodGcdToTorProxyHom, torProxyGeneratorIntHom]
""",
        "Mock1 quotient generator",
    )
    changed |= c

    text = text.replace("← Nat.cast_min, ", "")
    text = text.replace(", ← Nat.cast_min", "")
    text = text.replace("← Nat.cast_min", "")
    text = text.replace(
        "exact ⟨Matrix.invertibleOfIsUnitDet hunit⟩",
        "exact ⟨Matrix.invertibleOfIsUnitDet (MahlerMatrix N R) hunit⟩",
    )

    text, c = replace_once(
        text,
        """theorem finiteMahlerEval_eq_mahlerMatrix_mulVec {N : ℕ} {R : Type*} [Semiring R]
    (coeffs : Fin (N + 1) → R) (n : Fin (N + 1)) :
    finiteMahlerEval coeffs n.val = (MahlerMatrix N R).mulVec coeffs n := by
  simp [finiteMahlerEval, MahlerMatrix, Matrix.mulVec]
""",
        """theorem finiteMahlerEval_eq_mahlerMatrix_mulVec {N : ℕ} {R : Type*} [Semiring R]
    (coeffs : Fin (N + 1) → R) (n : Fin (N + 1)) :
    finiteMahlerEval coeffs n.val = (MahlerMatrix N R).mulVec coeffs n := by
  rfl
""",
        "Mock1 finite evaluation is matrix multiplication",
    )
    changed |= c

    text = text.replace(
        """  rw [finiteDifferenceCoeff_formula]
  rfl

/-- The finite-difference matrix""",
        """  rw [finiteDifferenceCoeff_formula]

/-- The finite-difference matrix""",
    )
    text = text.replace(
        "rw [← Matrix.mulVec_mulVec, mahlerMatrix_mul_mahlerInverseMatrix]",
        "rw [Matrix.mulVec_mulVec, mahlerMatrix_mul_mahlerInverseMatrix]",
    )

    for name in (
        "padic_normalization_finite_corrected",
        "padic_finite_normalization_corrected",
        "zmod_finiteMahlerCertificate_of_engine",
        "zmod_finiteMahlerCertificate_of_samples",
    ):
        text2, n = re.subn(rf"\btheorem {name}\b", f"noncomputable def {name}", text, count=1)
        if n:
            text, changed = text2, True
            print(f"Mock1 {name}: changed theorem to noncomputable def")

    text = re.sub(r"(?<![A-Za-z0-9_.])Tendsto\b", "Filter.Tendsto", text)
    text = re.sub(r"(?<![A-Za-z0-9_.])atTop\b", "Filter.atTop", text)

    text2, n = re.subn(
        r"([∑∏])\s+([A-Za-z_][A-Za-z0-9_']*)\s+in\s+",
        r"\1 \2 ∈ ",
        text,
    )
    if n:
        text, changed = text2, True
        print(f"Mock1 big-operator binder syntax: applied {n} replacements")

    text = text.replace(
        "norm_num [pdfMahlerEvalZMod25",
        "norm_num [Nat.choose, pdfMahlerEvalZMod25",
    )
    text = text.replace(
        "norm_num [finiteMahlerEval, pdfMahler",
        "norm_num [Nat.choose, finiteMahlerEval, pdfMahler",
    )

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("Mock1 first-pass repairs changed source.")
    else:
        print("No Mock1 first-pass changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
