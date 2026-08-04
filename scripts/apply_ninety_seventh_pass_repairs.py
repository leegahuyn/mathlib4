from __future__ import annotations

from pathlib import Path

import apply_ninety_sixth_pass_repairs as pass96
import apply_seventy_first_pass_repairs as pass71

ROOT = Path("PrimalitySheafVerification")
replace_exact = pass71.replace_exact


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem inverseDerivative_conjugate_term
    (g : LocalFrameChange (X := X) (U := U)) (A : Omega X 1 U) :
    matrixWedge (matrixWedge (matrixDifferential g.inverse) A) g.forward =
      -matrixWedge g.pureGauge (g.conjugateOne A) := by
  rw [g.differential_inverse]
  have hnormalize :
      matrixWedge
          (matrixWedge
            (matrixWedge g.pureGauge g.inverse) A) g.forward =
        matrixWedge g.pureGauge (g.conjugateOne A) := by
    unfold conjugateOne
    calc
      matrixWedge
          (matrixWedge (matrixWedge g.pureGauge g.inverse) A) g.forward =
          matrixWedge
            (matrixWedge g.pureGauge (matrixWedge g.inverse A)) g.forward := by
        rw [show matrixWedge (matrixWedge g.pureGauge g.inverse) A =
            matrixWedge g.pureGauge (matrixWedge g.inverse A) by
          simpa using matrixWedge_assoc g.pureGauge g.inverse A]
      _ = matrixWedge g.pureGauge
            (matrixWedge (matrixWedge g.inverse A) g.forward) := by
        simpa using
          matrixWedge_assoc g.pureGauge (matrixWedge g.inverse A) g.forward
  rw [matrixWedge_neg_left, matrixWedge_neg_left, hnormalize]
"""
    new = """theorem inverseDerivative_conjugate_term
    (g : LocalFrameChange (X := X) (U := U)) (A : Omega X 1 U) :
    matrixWedge (matrixWedge (matrixDifferential g.inverse) A) g.forward =
      -matrixWedge g.pureGauge (g.conjugateOne A) := by
  have hnormalize :
      matrixWedge
          (matrixWedge
            (matrixWedge g.pureGauge g.inverse) A) g.forward =
        matrixWedge g.pureGauge (g.conjugateOne A) := by
    unfold conjugateOne
    calc
      matrixWedge
          (matrixWedge (matrixWedge g.pureGauge g.inverse) A) g.forward =
          matrixWedge
            (matrixWedge g.pureGauge (matrixWedge g.inverse A)) g.forward := by
        rw [show matrixWedge (matrixWedge g.pureGauge g.inverse) A =
            matrixWedge g.pureGauge (matrixWedge g.inverse A) by
          simpa using matrixWedge_assoc g.pureGauge g.inverse A]
      _ = matrixWedge g.pureGauge
            (matrixWedge (matrixWedge g.inverse A) g.forward) := by
        simpa using
          matrixWedge_assoc g.pureGauge (matrixWedge g.inverse A) g.forward
  calc
    matrixWedge (matrixWedge (matrixDifferential g.inverse) A) g.forward =
        matrixWedge
          (matrixWedge (-matrixWedge g.pureGauge g.inverse) A) g.forward := by
      rw [g.differential_inverse]
    _ = -matrixWedge
          (matrixWedge (matrixWedge g.pureGauge g.inverse) A) g.forward := by
      rw [matrixWedge_neg_left, matrixWedge_neg_left]
    _ = -matrixWedge g.pureGauge (g.conjugateOne A) := by
      rw [hnormalize]
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2 normalize the inverse derivative conjugate term by calc")
    changed |= did

    old = """theorem inverseDerivative_differential_term
    (g : LocalFrameChange (X := X) (U := U)) :
    matrixWedge (matrixDifferential g.inverse)
        (matrixDifferential g.forward) =
      -matrixWedge g.pureGauge g.pureGauge := by
  rw [g.differential_inverse]
  have hnormalize :
      matrixWedge
          (matrixWedge g.pureGauge g.inverse)
          (matrixDifferential g.forward) =
        matrixWedge g.pureGauge g.pureGauge := by
    unfold pureGauge
    simpa using matrixWedge_assoc g.pureGauge g.inverse
      (matrixDifferential g.forward)
  rw [matrixWedge_neg_left, hnormalize]
"""
    new = """theorem inverseDerivative_differential_term
    (g : LocalFrameChange (X := X) (U := U)) :
    matrixWedge (matrixDifferential g.inverse)
        (matrixDifferential g.forward) =
      -matrixWedge g.pureGauge g.pureGauge := by
  have hnormalize :
      matrixWedge
          (matrixWedge g.pureGauge g.inverse)
          (matrixDifferential g.forward) =
        matrixWedge g.pureGauge g.pureGauge := by
    unfold pureGauge
    simpa using matrixWedge_assoc g.pureGauge g.inverse
      (matrixDifferential g.forward)
  calc
    matrixWedge (matrixDifferential g.inverse)
        (matrixDifferential g.forward) =
      matrixWedge (-matrixWedge g.pureGauge g.inverse)
        (matrixDifferential g.forward) := by
      rw [g.differential_inverse]
    _ = -matrixWedge (matrixWedge g.pureGauge g.inverse)
        (matrixDifferential g.forward) := by
      rw [matrixWedge_neg_left]
    _ = -matrixWedge g.pureGauge g.pureGauge := by
      rw [hnormalize]
"""
    text, did = replace_exact(
        text, old, new, 1,
        "Mock2 normalize the inverse derivative differential term by calc")
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    start = text.index("namespace GenuineWeightedSobolev")
    end = text.index("end GenuineWeightedSobolev", start)
    block = text[start:end]
    for old_name, new_name in [
        ("GenuineInverseHalfWeightAutomorphy.IsAutomorphic",
         "GenuineHalfWeightAutomorphy.IsAutomorphic"),
        ("GenuineInverseHalfWeightAutomorphy.IsAEAutomorphic",
         "GenuineHalfWeightAutomorphy.IsAEAutomorphic"),
    ]:
        count = block.count(old_name)
        if count:
            block = block.replace(old_name, new_name)
            changed = True
            print(f"Mock2Advanced restore {new_name}: applied {count}")
    explicit = "exact (M.core_equivariant v hv).isAE μ)"
    implicit = "exact (M.core_equivariant v hv).isAE)"
    if explicit in block:
        block = block.replace(explicit, implicit, 1)
        changed = True
        print("Mock2Advanced restore implicit measure in the genuine half-weight completion: applied 1")
    text = text[:start] + block + text[end:]

    replacements = [
        ("""  rw [cuspPowerDensity_integrable_iff hY]
  unfold basicGrowth
  linarith
""",
         """  rw [cuspPowerDensity_integrable_iff hY]
  unfold basicGrowth
  constructor <;> intro h <;> linarith
""",
         "Mock2Advanced split the exact basic power window"),
        ("""  rw [cuspPowerDensity_integrable_iff hY]
  unfold rankinSelbergGrowth basicGrowth
  linarith
""",
         """  rw [cuspPowerDensity_integrable_iff hY]
  unfold rankinSelbergGrowth basicGrowth
  constructor <;> intro h <;> linarith
""",
         "Mock2Advanced split the exact Rankin-Selberg power window"),
        ("""  rw [rankinSelberg_power_integrable_iff hY,
    eisensteinGrowth_eq_self (by linarith : 1 / 2 ≤ σ)]
  linarith
""",
         """  rw [rankinSelberg_power_integrable_iff hY,
    eisensteinGrowth_eq_self (by linarith : 1 / 2 ≤ σ)]
  constructor <;> intro h <;> linarith
""",
         "Mock2Advanced split the beta-one Rankin-Selberg window"),
        ("""  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hY]
  linarith
""",
         """  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hY]
  constructor <;> intro h <;> linarith
""",
         "Mock2Advanced split the near-zero beta-one window"),
    ]
    for old_text, new_text, label in replacements:
        text, did = replace_exact(text, old_text, new_text, 1, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """theorem gammaTwoOpenCarrier_isOpen : IsOpen gammaTwoOpenCarrier := by
  unfold gammaTwoOpenCarrier
  refine isOpen_iUnion fun q ↦ ?_
  exact ModularGroup.isOpen_fdo.smul (gammaTwoCosetRep q)
"""
    new = """theorem gammaTwoOpenCarrier_isOpen : IsOpen gammaTwoOpenCarrier := by
  unfold gammaTwoOpenCarrier
  refine isOpen_iUnion fun q ↦ ?_
  let g : SL(2, ℤ) := gammaTwoCosetRep q
  have hset :
      g • ModularGroup.fdo =
        (fun z : ℍ => g⁻¹ • z) ⁻¹' ModularGroup.fdo := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_smul_set.mp hz with ⟨w, hw, rfl⟩
      simpa using hw
    · intro hz
      exact Set.mem_smul_set.mpr ⟨g⁻¹ • z, hz, by simp⟩
  rw [hset]
  exact ModularGroup.isOpen_fdo.preimage (continuous_sl2z_smul g⁻¹)
"""
    text, did = replace_exact(
        text, old, new, 1,
        "FunctionalAnalysis prove openness of modular translates by inverse preimage")
    changed |= did

    marker = """/-- All translates of the boundary omitted from the full modular open tile. -/
"""
    insertion = """noncomputable instance sl2zCountable : Countable (SL(2, ℤ)) :=
  (show Function.Injective
      (fun γ : SL(2, ℤ) =>
        ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
         (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) from by
      intro a b h
      apply Matrix.SpecialLinearGroup.ext
      funext i j
      fin_cases i <;> fin_cases j <;> simp_all).countable

"""
    if insertion not in text:
        if marker not in text:
            raise RuntimeError("FunctionalAnalysis SL2 countability insertion marker absent")
        text = text.replace(marker, insertion + marker, 1)
        changed = True
        print("FunctionalAnalysis construct countability of SL2Z from four entries: applied")

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    pass96.main()
    repair_mock2()
    repair_mock2_advanced()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
