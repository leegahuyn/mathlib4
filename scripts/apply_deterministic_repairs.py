from __future__ import annotations

import re
from pathlib import Path

ROOT = Path("PrimalitySheafVerification")
IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+\S")


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


def repair_spt1() -> bool:
    path = ROOT / "Spt1.lean"
    changed = False
    replacements = (
        ("padicValRat.pow (p := p) (q := (-1 : ℚ)) hm1,",
         "padicValRat.pow (p := p) (-1 : ℚ),",
         "Spt1 obsolete padicValRat.pow sign call"),
        ("padicValRat.pow (p := p) (q := (u : ℚ)) huq,",
         "padicValRat.pow (p := p) (u : ℚ),",
         "Spt1 obsolete padicValRat.pow integer call"),
        ("padicValRat.pow (p := p) (q := u) hu0,",
         "padicValRat.pow (p := p) u,",
         "Spt1 obsolete padicValRat.pow rational call"),
        ("≤ X.minFac * (X / X.minFac) := mul_le_mul_left' h _",
         "≤ X.minFac * (X / X.minFac) := Nat.mul_le_mul_left X.minFac h",
         "Spt1 multiplication monotonicity API"),
        ("""theorem resC_d10 (N : ℕ) : (resC N).d 1 0 = mulN N :=
  by
    simpa [resC, df] using
      (ChainComplex.of_d Xf (df N) (resC_sq N) 0)
""",
         """theorem resC_d10 (N : ℕ) : (resC N).d 1 0 = mulN N := by
  dsimp [resC, df]
  rfl
""",
         "Spt1 compute resC differential 1-to-0 definitionally"),
        ("""theorem resC_d21 (N : ℕ) : (resC N).d 2 1 = 0 :=
  by
    simpa [resC, df] using
      (ChainComplex.of_d Xf (df N) (resC_sq N) 1)
""",
         """theorem resC_d21 (N : ℕ) : (resC N).d 2 1 = 0 := by
  dsimp [resC, df]
  rfl
""",
         "Spt1 compute resC differential 2-to-1 definitionally"),
        ("theorem mulN_mono (N : ℕ) [NeZero N] : Mono (mulN N) := by\n",
         "set_option maxHeartbeats 800000 in\ntheorem mulN_mono (N : ℕ) [NeZero N] : Mono (mulN N) := by\n",
         "Spt1 local heartbeat budget for categorical mono elaboration"),
        ("""      have h2 : (p : ℝ) ^ padicValNat p n ≤ (p : ℝ) ^ (n - 1) := by
        gcongr
        exact hp1
""",
         """      have h2 : (p : ℝ) ^ padicValNat p n ≤ (p : ℝ) ^ (n - 1) := by
        gcongr
""",
         "Spt1 remove tactic after gcongr closes the goal"),
        ("""    rw [key, hnorm, hsplit]
    calc ‖x‖ ^ (n - 1) * ‖x‖ * (p : ℝ) ^ padicValNat p n
        = ‖x‖ * (‖x‖ ^ (n - 1) * (p : ℝ) ^ padicValNat p n) := by ring
      _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left hclaim (norm_nonneg x)
      _ = ‖x‖ := mul_one _
""",
         """    calc
      ‖padicLogSeries x n‖
          = ‖x‖ ^ n * ‖(n : ℚ_[p])‖⁻¹ := key
      _ = (‖x‖ ^ (n - 1) * ‖x‖) * (p : ℝ) ^ padicValNat p n := by
            rw [hnorm, hsplit]
      _ = ‖x‖ * (‖x‖ ^ (n - 1) * (p : ℝ) ^ padicValNat p n) := by ring
      _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left hclaim (norm_nonneg x)
      _ = ‖x‖ := mul_one _
""",
         "Spt1 explicit padic log norm calculation"),
    )
    for old, new, label in replacements:
        changed = replace_once(path, old, new, label) or changed
    return changed


def repair_spt2() -> bool:
    path = ROOT / "Spt2.lean"
    return replace_once(
        path,
        """          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
            show Ideal.Quotient.mk (Ideal.span {f}) a
                = a • (1 : (ZMod p)[X] ⧸ Ideal.span {f}) from by
              rw [← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one],
            TensorProduct.smul_tmul]
""",
        """          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
            show Ideal.Quotient.mk (Ideal.span {f}) a
                = a • (1 : (ZMod p)[X] ⧸ Ideal.span {f}) from by
              change ((Ideal.Quotient.mk (Ideal.span {f}) a) :
                (ZMod p)[X] ⧸ Ideal.span {f}) =
                  ((Ideal.Quotient.mk (Ideal.span {f}) a) :
                    (ZMod p)[X] ⧸ Ideal.span {f}) • 1
              simpa [smul_eq_mul],
            TensorProduct.smul_tmul]
""",
        "Spt2 quotient scalar identity",
    )


def repair_spt7() -> bool:
    path = ROOT / "Spt7.lean"
    changed = False
    changed = replace_once(
        path,
        """theorem standardIntResolutionAugmentation_f_zero (M : ℕ) :
    (standardIntResolutionAugmentation M).f 0 =
      ModuleCat.ofHom
        (((standardIntResolutionQuotient M) : AddMonoidHom ℤ (ZMod M)).toIntLinearMap) := by
  simp [standardIntResolutionAugmentation]
""",
        """theorem standardIntResolutionAugmentation_f_zero (M : ℕ) :
    (standardIntResolutionAugmentation M).f 0 =
      ModuleCat.ofHom
        (((standardIntResolutionQuotient M) : AddMonoidHom ℤ (ZMod M)).toIntLinearMap) := by
  rfl
""",
        "Spt7 augmentation degree-zero component",
    ) or changed
    changed = replace_once(
        path,
        """theorem koszulR1Differential_sq (r : R) (n : ℕ) :
    koszulR1Differential (M := M) r (n + 1) ≫
      koszulR1Differential (M := M) r n = 0 := by
  cases n <;> simp [koszulR1Differential]
""",
        """theorem koszulR1Differential_sq (r : R) (n : ℕ) :
    koszulR1Differential (M := M) r (n + 1) ≫
      koszulR1Differential (M := M) r n = 0 := by
  cases n with
  | zero => simp only [koszulR1Differential_succ, zero_comp]
  | succ n => simp only [koszulR1Differential_succ, zero_comp]
""",
        "Spt7 one-element Koszul square-zero proof",
    ) or changed
    changed = replace_once(
        path,
        """  | succ n =>
      cases n <;> simp [koszulR2Differential]
""",
        """  | succ n =>
      cases n with
      | zero => simp only [koszulR2Differential_succ_succ, zero_comp]
      | succ n => simp only [koszulR2Differential_succ_succ, zero_comp]
""",
        "Spt7 two-element Koszul higher square-zero proof",
    ) or changed
    changed = replace_once(path, "PowerSeries.derivative_subst (A := K)",
                           "PowerSeries.derivative_subst (R := K)",
                           "Spt7 derivative_subst parameter rename") or changed
    return changed


def repair_qym_import() -> bool:
    path = ROOT / "QYM.lean"
    text = path.read_text(encoding="utf-8-sig")
    lines = text.splitlines()
    import_indices = [i for i, line in enumerate(lines) if IMPORT_RE.match(line)]
    if not import_indices:
        return False
    first_nonempty = next((i for i, line in enumerate(lines) if line.strip()), len(lines))
    if import_indices == list(range(first_nonempty, first_nonempty + len(import_indices))):
        return False
    imports = [lines[i].strip() for i in import_indices]
    index_set = set(import_indices)
    remaining = [line for i, line in enumerate(lines) if i not in index_set]
    while remaining and not remaining[0].strip():
        remaining.pop(0)
    path.write_text("\n".join(imports) + "\n\n" + "\n".join(remaining).rstrip() + "\n",
                    encoding="utf-8", newline="\n")
    print("QYM: moved all imports to the beginning")
    return True


def main() -> int:
    changed = False
    changed = repair_spt1() or changed
    changed = repair_spt2() or changed
    changed = repair_spt7() or changed
    changed = repair_qym_import() or changed
    print("Deterministic repairs changed sources." if changed else "No source changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
