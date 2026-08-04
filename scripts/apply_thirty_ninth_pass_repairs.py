from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0:
        if new in text:
            print(f"{label}: already applied")
            return text, False
        print(f"{label}: source changed; skipped")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  residual_not_mem_theorem := by
    intro h
    cases h
""",
            """  residual_not_mem_theorem := by
    decide
""",
            "Mock1Advanced decide the closed residual-table nonmembership",
        ),
        (
            """theorem mem_all (c : RemainingAdvancedClaim) :
    List.Mem c all := by
  cases c <;> simp [all]
""",
            """theorem mem_all (c : RemainingAdvancedClaim) :
    List.Mem c all := by
  cases c with
  | abstractCertificate => exact List.Mem.head _
  | concreteCertificate => exact List.Mem.tail _ (List.Mem.head _)
  | claimRegistry => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | objectCoefficientSchema =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | paperObjectDataInstance =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _))))
  | scalarJacobiDegeneracyRelation =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  | principalPartRationalSolve =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | completionShadowHolomorphic =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))
  | cuspTransport =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  | appellLerchBlockFormula =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  | principalExponentFormula =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.head _))))))))))
  | fixedShadowUnaryTheta =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  | insideOutsideQSeries =>
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.head _))))))))))))
""",
            "Mock1Advanced prove the thirteen remaining claims structurally",
        ),
        (
            """  m_mem := by
    simp [referenceMock1MList]
  r_mem := by
    simp [referenceMock1RPhases]
""",
            """  m_mem := List.Mem.head _
  r_mem := List.Mem.head _
""",
            "Mock1Advanced certify the Appell-Lerch parameter memberships directly",
        ),
        (
            """  m_mem := by
    simp [referenceMock1MList]
  formula_eq := by
""",
            """  m_mem := List.Mem.head _
  formula_eq := by
""",
            "Mock1Advanced certify the principal-exponent parameter membership directly",
        ),
        (
            """theorem reference_paper_depth_one_matvec_eq_rhs :
    MatVecRat referencePaperDepthOneMatrix referencePaperDepthOneSolution =
      referencePaperDepthOneRHS := by
  decide
""",
            """theorem reference_paper_depth_one_matvec_eq_rhs :
    MatVecRat referencePaperDepthOneMatrix referencePaperDepthOneSolution =
      referencePaperDepthOneRHS := by
  norm_num [MatVecRat, dotRat, referencePaperDepthOneMatrix,
    referencePaperDepthOneSolution, referencePaperDepthOneRHS]
""",
            "Mock1Advanced compute the depth-one rational matrix product",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """  change
    (((p ^ shiftExponent M p k) *
        (p ^ thicknessExponent M p k) : ℕ) : ZMod (Pk p k)) = 0
  exact h
""",
            """  simpa only [Nat.cast_mul, Nat.cast_pow, Int.cast_pow,
    Int.cast_natCast] using h
""",
            "Mock2 normalize both natural and integer power casts in the modulus proof",
        ),
        (
            """  simpa only [powerShiftHom] using
    (ZMod.lift_coe (p ^ thicknessExponent M p k)
      ⟨powerShiftIntegerHom M p k,
        powerShiftIntegerHom_modulus_eq_zero M p k⟩ z)
""",
            """  rw [powerShiftHom]
  calc
    (ZMod.lift (p ^ thicknessExponent M p k)
        ⟨powerShiftIntegerHom M p k,
          powerShiftIntegerHom_modulus_eq_zero M p k⟩)
        (z : ZMod (p ^ thicknessExponent M p k)) =
      powerShiftIntegerHom M p k z :=
        ZMod.lift_coe (p ^ thicknessExponent M p k)
          ⟨powerShiftIntegerHom M p k,
            powerShiftIntegerHom_modulus_eq_zero M p k⟩ z
    _ = (p ^ shiftExponent M p k : ZMod (Pk p k)) *
        (z : ZMod (Pk p k)) :=
      powerShiftIntegerHom_apply M p k z
""",
            "Mock2 compose lift_coe with the integer-hom application formula",
        ),
        (
            """    simpa only [Int.cast_mul, Int.cast_natCast,
      Nat.cast_pow] using hz
""",
            """    simpa only [Int.cast_mul, Int.cast_pow,
      Int.cast_natCast] using hz
""",
            "Mock2 normalize the injectivity integer power cast",
        ),
        (
            """      simpa only [Int.cast_mul, Int.cast_natCast,
        Nat.cast_pow] using hpz
""",
            """      simpa only [Int.cast_mul, Int.cast_pow,
        Int.cast_natCast] using hpz
""",
            "Mock2 normalize the surjectivity integer power cast",
        ),
        (
            """    rw [powerShiftHom_intCast]
    change ((((p ^ shiftExponent M p k : ℕ) : ℤ) * q : ℤ) :
      ZMod (Pk p k)) = (z : ZMod (Pk p k))
    simpa [hs, hq]
""",
            """    rw [powerShiftHom_intCast, hs, hq]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
""",
            "Mock2 finish the positive-valuation surjectivity branch by cast normalization",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_functional_analysis() -> None:
    path = ROOT / "Mock2_FunctionalAnalysis.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    replacements = [
        (
            """              rw [hr, map_smulₛₗ]
              change r * (F v).re - 0 * (F v).im = r * (F v).re
              ring }
""",
            """              rw [hr, map_smulₛₗ]
              simp only [starRingEnd_apply, Complex.star_def,
                Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul] }
""",
            "FunctionalAnalysis normalize real scalar anti-linearity with re_ofReal_mul",
        ),
        (
            """            rw [hr, map_smulₛₗ]
            change r * (B u v).re - 0 * (B u v).im = r * (B u v).re
            ring)
""",
            """            rw [hr, map_smulₛₗ]
            simp only [starRingEnd_apply, Complex.star_def,
              Complex.conj_ofReal, smul_eq_mul, Complex.re_ofReal_mul])
""",
            "FunctionalAnalysis normalize form anti-linearity with re_ofReal_mul",
        ),
        (
            """theorem solve_spec
    (d : FredholmBypassData A) (F : W) :
    A (d.solve F) = F := by
  rw [← d.unshiftedEquiv_apply (d.solve F)]
  simpa only [solve, solutionOperator] using
    d.unshiftedEquiv.apply_symm_apply F
""",
            """theorem solve_spec
    (d : FredholmBypassData A) (F : W) :
    A (d.solve F) = F := by
  rw [← d.unshiftedEquiv_apply (d.solve F)]
  unfold solve solutionOperator
  exact d.unshiftedEquiv.apply_symm_apply F
""",
            "FunctionalAnalysis unfold the continuous inverse before apply_symm_apply",
        ),
    ]

    for old, new, label in replacements:
        text, did = replace_once(text, old, new, label)
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_functional_analysis()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
