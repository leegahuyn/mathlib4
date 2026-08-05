from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        "liftedBq (v := v) A",
        "liftedBq.{v} A",
        "Mock2 specify the lifted boundary universe explicitly",
        expected=4,
    )
    m2 = replace_exact(
        m2,
        "liftedBq_isSheaf (v := v) A",
        "liftedBq_isSheaf.{v} A",
        "Mock2 specify the lifted sheaf proof universe explicitly",
        expected=3,
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        "{R : Type*} [CommField R] [LinearOrder R] [IsStrictOrderedRing R]",
        "{R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]",
        "Mock2 Advanced restore the current commutative Field class",
        expected=2,
    )
    m2a = replace_exact(
        m2a,
        """    energy + boundary = rhs ↔ energy = rhs - boundary := by
  constructor <;> intro h <;> linear_combination h
""",
        """    energy + boundary = rhs ↔ energy = rhs - boundary := by
  constructor
  · intro h
    calc
      energy = (energy + boundary) - boundary := by simp
      _ = rhs - boundary := congrArg (fun t : R => t - boundary) h
  · intro h
    calc
      energy + boundary = (rhs - boundary) + boundary :=
        congrArg (fun t : R => t + boundary) h
      _ = rhs := by simp
""",
        "Mock2 Advanced prove the boundary rewrite additively",
    )
    m2a = replace_exact(
        m2a,
        """    have hexp :
        Complex.exp
            (((k : ℂ) * Real.pi * Complex.I) * (2 : ℝ)) = 1 := by
      rw [show
        ((k : ℂ) * Real.pi * Complex.I) * (2 : ℝ) =
          (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
""",
        """    have hexp :
        Complex.exp
            (((k : ℂ) * Real.pi * Complex.I) * (2 : ℝ)) = 1 := by
      have htwo : (((2 : ℝ) : ℂ)) = (2 : ℂ) := by norm_num
      rw [htwo]
      rw [show
        ((k : ℂ) * Real.pi * Complex.I) * (2 : ℂ) =
          (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
""",
        "Mock2 Advanced normalize the width-two endpoint cast",
    )
    m2a = replace_exact(
        m2a,
        """  simp only [mode]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
""",
        """  simp only [mode]
  have hstar :
      star (Complex.exp ((n : ℂ) * Real.pi * Complex.I * (x : ℂ))) =
        Complex.exp
          (star ((n : ℂ) * Real.pi * Complex.I * (x : ℂ))) := by
    simpa using
      (Complex.exp_conj
        ((n : ℂ) * Real.pi * Complex.I * (x : ℂ))).symm
  rw [hstar, ← Complex.exp_add]
  congr 1
""",
        "Mock2 Advanced rewrite conjugated exponentials through star",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """    have hEtaTarget : DifferentiableAt ℂ
        (fun u : ℂ ↦ ModularForm.eta
          ((g • UpperHalfPlane.ofComplex u : ℍ) : ℂ)) w := by
      simpa only [Function.comp_apply] using
        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
          hTargetMem).comp w hAction
""",
        """    have hEtaTarget : DifferentiableAt ℂ
        (fun u : ℂ ↦ ModularForm.eta
          ((g • UpperHalfPlane.ofComplex u : ℍ) : ℂ)) w := by
      change DifferentiableAt ℂ
        (ModularForm.eta ∘
          fun u : ℂ ↦ ((g • UpperHalfPlane.ofComplex u : ℍ) : ℂ)) w
      exact
        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
          hTargetMem).comp w hAction
""",
        "FunctionalAnalysis expose the eta composition definitionally",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
