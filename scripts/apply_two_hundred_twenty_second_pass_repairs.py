from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected exactly 1 match, found {count}")
    print(f"{label}: applied 1")
    return text.replace(old, new, 1)


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """variable {E_G H_G G : Type*}
variable [NormedAddCommGroup E_G] [NormedSpace ℂ E_G] [CompleteSpace E_G]
variable [TopologicalSpace H_G]
variable (I_G : ModelWithCorners ℂ E_G H_G)
variable [Group G] [TopologicalSpace G] [ChartedSpace H_G G]
""",
        """variable {E_G H_G : Type*}
variable [NormedAddCommGroup E_G] [NormedSpace ℂ E_G] [CompleteSpace E_G]
variable [TopologicalSpace H_G]
variable (I_G : ModelWithCorners ℂ E_G H_G)
variable (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H_G G]
""",
        "Mock2 make the gauge group an explicit parameter after the model",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """inductive ModularBoundaryPiece
  | arc
  | left
  | right
  deriving DecidableEq, Fintype, Repr
""",
        """inductive ModularBoundaryPiece
  | arc
  | left
  | right
  deriving DecidableEq, Repr

instance : Fintype ModularBoundaryPiece where
  elems := {.arc, .left, .right}
  complete := by
    intro x
    cases x <;> simp
""",
        "Mock2 Advanced define the three boundary pieces by an explicit Fintype",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """        calc
          Bw = 1 * Bw := by rw [one_mul]
          _ = (star (j ^ 2) * star (j ^ 2)⁻¹) * Bw :=
            congrArg (fun z : ℂ => z * Bw) (mul_inv_cancel₀ hs).symm
          _ = star (j ^ 2) * (star (j ^ 2)⁻¹ * Bw) :=
            mul_assoc _ _ _
""",
        """        have hstarInv :
            star ((j ^ 2)⁻¹) = (star (j ^ 2))⁻¹ := by
          simp only [map_inv₀]
        calc
          Bw = 1 * Bw := by rw [one_mul]
          _ = (star (j ^ 2) * (star (j ^ 2))⁻¹) * Bw :=
            congrArg (fun z : ℂ => z * Bw) (mul_inv_cancel₀ hs).symm
          _ = star (j ^ 2) * ((star (j ^ 2))⁻¹ * Bw) :=
            mul_assoc _ _ _
          _ = star (j ^ 2) * (star ((j ^ 2)⁻¹) * Bw) := by
            rw [hstarInv]
""",
        "FunctionalAnalysis distinguish star of an inverse from inverse of a star",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
