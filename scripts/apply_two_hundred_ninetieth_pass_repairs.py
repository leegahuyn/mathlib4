from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def main() -> int:
    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        "ContDiff ℂ ∞",
        "ContDiff ℂ ⊤",
        "Mock2 Advanced use the current infinite differentiability order",
        expected=15,
    )
    m2a = replace_exact(
        m2a,
        """  add_mem' := by
    intro A B hA hB
    simpa only [IsSmooth, Pi.add_apply, map_add] using hA.add hB
  smul_mem' := by
    intro c A hA
    simpa only [IsSmooth, Pi.smul_apply, map_smul] using hA.const_smul c
""",
        """  add_mem' := by
    intro A B hA hB
    change ContDiff ℂ ⊤ (fun z => coordinate (A z)) at hA
    change ContDiff ℂ ⊤ (fun z => coordinate (B z)) at hB
    change ContDiff ℂ ⊤ (fun z => coordinate ((A + B) z))
    simpa only [Pi.add_apply, map_add] using hA.add hB
  smul_mem' := by
    intro c A hA
    change ContDiff ℂ ⊤ (fun z => coordinate (A z)) at hA
    change ContDiff ℂ ⊤ (fun z => coordinate ((c • A) z))
    simpa only [Pi.smul_apply, map_smul] using hA.const_smul c
""",
        "Mock2 Advanced algebraic smooth-form submodule laws",
    )
    m2a = replace_exact(
        m2a,
        """  zero_mem' := by
    simpa using
      (contDiff_const : ContDiff ℂ ⊤ (fun _ : ℂ => (0 : ContinuousValue)))
  add_mem' := by
    intro A B hA hB
    simpa only [Pi.add_apply] using hA.add hB
  smul_mem' := by
    intro c A hA
    simpa only [Pi.smul_apply] using hA.const_smul c
""",
        """  zero_mem' := by
    change ContDiff ℂ ⊤ (fun _ : ℂ => (0 : ContinuousValue))
    exact contDiff_const
  add_mem' := by
    intro A B hA hB
    change ContDiff ℂ ⊤ (fun z => A z + B z)
    exact hA.add hB
  smul_mem' := by
    intro c A hA
    change ContDiff ℂ ⊤ (fun z => c • A z)
    exact hA.const_smul c
""",
        "Mock2 Advanced continuous smooth-form submodule laws",
    )
    m2a = replace_exact(
        m2a,
        """def forgetContinuousValue (A : ContinuousValue) : AlgebraicValue where
  toFun v := (A v).toLinearMap
  map_add' v w := by
    ext x
    simp
  map_smul' c v := by
    ext x
    simp
""",
        """def forgetContinuousValue (A : ContinuousValue) : AlgebraicValue where
  toFun v := (A v).toLinearMap
  map_add' v w :=
    congrArg ContinuousLinearMap.toLinearMap (A.map_add v w)
  map_smul' c v :=
    congrArg ContinuousLinearMap.toLinearMap (A.map_smul c v)
""",
        "Mock2 Advanced forget continuity through bundled map laws",
    )
    m2a = replace_exact(
        m2a,
        """namespace UnnumberedFormulaLedger

inductive Disposition
  | proved
  | correctedAndProved
  | removedWithErratum
  deriving DecidableEq, Fintype, Repr
""",
        """namespace UnnumberedFormulaLedger

inductive Disposition
  | proved
  | correctedAndProved
  | removedWithErratum
  deriving DecidableEq, Repr

instance : Fintype Disposition where
  elems := {.proved, .correctedAndProved, .removedWithErratum}
  complete := by
    intro x
    cases x <;> simp
""",
        "Mock2 Advanced explicit disposition finite enumeration",
    )
    m2a = replace_exact(
        m2a,
        """  | equation5_1
  | equations6_1_to_6_18
  deriving DecidableEq, Fintype, Repr
""",
        """  | equation5_1
  | equations6_1_to_6_18
  deriving DecidableEq, Repr

instance : Fintype Claim where
  elems := {
    .item1_pp3_4,
    .equations1_1_to_1_16,
    .quotedQ2A_to_Q2F,
    .equations1_17_to_1_24,
    .equations1_26_to_1_30,
    .equations1_31_to_1_33,
    .equations2_1_to_2_4,
    .pages23_to_25,
    .equations3_1_to_3_6,
    .equations3_7_to_3_19,
    .equations3_20_to_3_26,
    .equations4_1_to_4_9,
    .equations4_10_to_4_27,
    .equations4_28_to_4_29,
    .equations4_30_to_4_32,
    .equation5_1,
    .equations6_1_to_6_18}
  complete := by
    intro x
    cases x <;> simp
""",
        "Mock2 Advanced explicit claim finite enumeration",
    )
    m2a = replace_exact(
        m2a,
        """theorem prototype_nonconstant : ¬ Function.Constant prototype := by
""",
        """namespace Function

/-- Compatibility predicate for an everywhere constant function. -/
def Constant {α β : Type*} (f : α → β) : Prop :=
  ∀ x y, f x = f y

end Function

theorem prototype_nonconstant : ¬ Function.Constant prototype := by
""",
        "Mock2 Advanced restore the constant-function predicate",
    )
    M2A.write_text(m2a, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
