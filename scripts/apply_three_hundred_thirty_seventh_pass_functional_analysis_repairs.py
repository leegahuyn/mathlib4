from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "204acd949c17f55013487819b215886ae5c1c5fb4d125d4683871f8fb94847ad"
EXPECTED_OUTPUT_SHA256 = "6e772d414fc0fb9b3ec532039a22a00f0d28e2884136bb0d841494d7bde3f2b1"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    print(f"{label}: expected=1 actual={count}")
    if count != 1:
        raise RuntimeError(f"{label}: expected one occurrence, found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass337] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass337 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    old_independence = """theorem potentialShellCoreZero_linearIndependent :
    LinearIndependent ℂ potentialShellCoreZero := by
  refine (linearIndependent_iff').2 ?_
  intro s g hsum N hNs
  have hEval := congrArg
    (fixedPhaseCoreEvaluation 0 (potentialShellPoint N)) hsum
  simp only [map_sum, map_smul, map_zero,
    fixedPhaseCoreEvaluation_apply, smul_eq_mul] at hEval
  have hOther : ∀ M ∈ s, M ≠ N →
      ((potentialShellCoreZero M : InverseEtaFixedPhaseCore 0) :
          SmoothQuotientCompactFunction) (potentialShellPoint N) = 0 := by
    intro M hMs hMN
    by_contra hMpoint
    exact Set.disjoint_left.mp
      (potentialShellCoreZero_support_pairwiseDisjoint hMN.symm)
      (potentialShellCoreZero_at_point_ne_zero N) hMpoint
  have hSingle :
      ∑ M ∈ s, g M *
          ((potentialShellCoreZero M : InverseEtaFixedPhaseCore 0) :
            SmoothQuotientCompactFunction) (potentialShellPoint N) =
        g N *
          ((potentialShellCoreZero N : InverseEtaFixedPhaseCore 0) :
            SmoothQuotientCompactFunction) (potentialShellPoint N) := by
    apply Finset.sum_eq_single_of_mem N hNs
    intro M hMs hMN
    rw [hOther M hMs hMN, mul_zero]
  rw [hSingle] at hEval
  exact (mul_eq_zero.mp hEval).resolve_right
    (potentialShellCoreZero_at_point_ne_zero N)

"""
    new_independence = """theorem potentialShellCoreZero_linearIndependent :
    LinearIndependent ℂ potentialShellCoreZero := by
  refine (linearIndependent_iff'ₛ).2 ?_
  intro s f g hsum N hNs
  have hEval := congrArg
    (fixedPhaseCoreEvaluation 0 (potentialShellPoint N)) hsum
  simp only [map_sum, map_smul,
    fixedPhaseCoreEvaluation_apply, smul_eq_mul] at hEval
  have hOther : ∀ M ∈ s, M ≠ N →
      ((potentialShellCoreZero M : InverseEtaFixedPhaseCore 0) :
          SmoothQuotientCompactFunction) (potentialShellPoint N) = 0 := by
    intro M hMs hMN
    by_contra hMpoint
    exact Set.disjoint_left.mp
      (potentialShellCoreZero_support_pairwiseDisjoint hMN.symm)
      (potentialShellCoreZero_at_point_ne_zero N) hMpoint
  have hF :
      ∑ M ∈ s, f M *
          ((potentialShellCoreZero M : InverseEtaFixedPhaseCore 0) :
            SmoothQuotientCompactFunction) (potentialShellPoint N) =
        f N *
          ((potentialShellCoreZero N : InverseEtaFixedPhaseCore 0) :
            SmoothQuotientCompactFunction) (potentialShellPoint N) := by
    apply Finset.sum_eq_single_of_mem N hNs
    intro M hMs hMN
    rw [hOther M hMs hMN, mul_zero]
  have hG :
      ∑ M ∈ s, g M *
          ((potentialShellCoreZero M : InverseEtaFixedPhaseCore 0) :
            SmoothQuotientCompactFunction) (potentialShellPoint N) =
        g N *
          ((potentialShellCoreZero N : InverseEtaFixedPhaseCore 0) :
            SmoothQuotientCompactFunction) (potentialShellPoint N) := by
    apply Finset.sum_eq_single_of_mem N hNs
    intro M hMs hMN
    rw [hOther M hMs hMN, mul_zero]
  rw [hF, hG] at hEval
  exact mul_right_cancel₀
    (potentialShellCoreZero_at_point_ne_zero N) hEval

/-- `InverseEtaFixedPhaseCore 0` is definitionally a complex submodule subtype.
Expose its canonical additive group only for APIs that require a ring module. -/
noncomputable local instance fixedPhaseCoreZeroAddCommGroup :
    AddCommGroup (InverseEtaFixedPhaseCore 0) :=
  Submodule.addCommGroup (inverseEtaFixedPhaseStableCoreSubmodule 0)

"""
    text = replace_once(
        text, old_independence, new_independence,
        "FunctionalAnalysis semiring linear-independence criterion and canonical group",
    )
    text = replace_once(
        text,
        "noncomputable def hyperbolicDensity (z : ℍ) : ℝ≥0 :=",
        "noncomputable def hyperbolicDensity (z : ℍ) : NNReal :=",
        "FunctionalAnalysis explicit NNReal density type",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass337 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass337] FunctionalAnalysis independence-instance and NNReal frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
