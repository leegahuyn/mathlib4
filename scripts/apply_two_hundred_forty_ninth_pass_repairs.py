from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"
M2A = ROOT / "PrimalitySheafVerification" / "Mock2_Advanced.lean"
FA = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new)


def replace_in_block(text: str, start: str, end: str, old: str, new: str,
                     expected: int, label: str) -> str:
    i = text.index(start)
    j = text.index(end, i)
    block = text[i:j]
    count = block.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} matches, found {count}")
    block = block.replace(old, new)
    print(f"{label}: applied {count}")
    return text[:i] + block + text[j:]


def main() -> int:
    m2 = M2.read_text(encoding="utf-8")
    m2 = replace_exact(
        m2,
        """abbrev OneFormValue
    (I_G : ModelWithCorners ℂ E_G H_G) (G : Type uGG) :=
  ℂ →L[ℂ] GaugeLieAlgebra I_G G

noncomputable local instance oneFormValueNormedAddCommGroup :
    NormedAddCommGroup (OneFormValue I_G G) := by
  change NormedAddCommGroup (ℂ →L[ℂ] GaugeLieAlgebra I_G G)
  infer_instance

noncomputable local instance oneFormValueNormedSpace :
    NormedSpace ℂ (OneFormValue I_G G) := by
  change NormedSpace ℂ (ℂ →L[ℂ] GaugeLieAlgebra I_G G)
  infer_instance

noncomputable local instance oneFormValueCoeFun :
    CoeFun (OneFormValue I_G G)
      (fun _ => ℂ → GaugeLieAlgebra I_G G) where
  coe L := fun z =>
    (show ℂ →L[ℂ] GaugeLieAlgebra I_G G from L) z
""",
        """abbrev OneFormValue
    (_I_G : ModelWithCorners ℂ E_G H_G) (_G : Type uGG) :=
  ℂ →L[ℂ] E_G
""",
        "Mock2 restore one-form values to the actual chart model",
    )
    m2 = replace_exact(
        m2,
        """noncomputable def gaugeAdjointValue (a : G) :
    GaugeLieAlgebra I_G G →L[ℂ] GaugeLieAlgebra I_G G :=
  mfderiv I_G I_G (fun x : G => a⁻¹ * x * a) 1
""",
        """noncomputable def gaugeAdjointValue (a : G) :
    E_G →L[ℂ] E_G :=
  mfderiv I_G I_G (fun x : G => a⁻¹ * x * a) 1
""",
        "Mock2 expose the adjoint derivative on the actual chart model",
    )
    m2 = replace_exact(
        m2,
        """    gaugeAdjointValue I_G G a =
      ContinuousLinearMap.id ℂ (GaugeLieAlgebra I_G G) := by
""",
        """    gaugeAdjointValue I_G G a =
      ContinuousLinearMap.id ℂ E_G := by
""",
        "Mock2 state the central adjoint identity on the chart model",
    )
    M2.write_text(m2, encoding="utf-8")

    m2a = M2A.read_text(encoding="utf-8")
    m2a = replace_exact(
        m2a,
        """attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] Complex.addCommGroup
attribute [-instance] Complex.instRing
attribute [-instance] Complex.instField
attribute [-instance] Complex.instDenselyNormedField

/-- Exact tangent formula for the cusp at zero. -/
theorem hasDerivAt_cuspZeroAmbientCurve {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) :
    HasDerivAt (cuspZeroAmbientCurve Y)
      (cuspFiniteAmbientTangent Y x) x := by
  have hneg :
      HasDerivAt (fun t : ℝ => -cuspHorizontalAmbientCurve Y t) (-1) x :=
    (hasDerivAt_cuspHorizontalAmbientCurve Y x).neg
  have hne : -cuspHorizontalAmbientCurve Y x ≠ 0 :=
    neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  letI : NontriviallyNormedField ℂ :=
    Complex.instDenselyNormedField.toNontriviallyNormedField
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    one_div] using hneg.inv hne
""",
        """/-- Exact tangent formula for the cusp at zero. -/
theorem hasDerivAt_cuspZeroAmbientCurve {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) :
    HasDerivAt (cuspZeroAmbientCurve Y)
      (cuspFiniteAmbientTangent Y x) x := by
  have haff :
      HasDerivAt
        (fun z : ℂ => -(z + (Y : ℂ) * Complex.I))
        (-1) (x : ℂ) := by
    simpa using
      (((hasDerivAt_id (x : ℂ)).add_const
        ((Y : ℂ) * Complex.I)).neg)
  have hne : -((x : ℂ) + (Y : ℂ) * Complex.I) ≠ 0 := by
    exact neg_ne_zero.mpr (cuspHorizontalAmbientCurve_ne_zero hY x)
  simpa [cuspZeroAmbientCurve, cuspFiniteAmbientTangent,
    cuspHorizontalAmbientCurve, one_div] using
      (haff.inv hne).comp_ofReal
""",
        "Mock2 Advanced differentiate the reciprocal over complex scalars then restrict",
    )
    m2a = replace_exact(
        m2a,
        """attribute [instance] Complex.instDenselyNormedField
attribute [instance] Complex.instField
attribute [instance] Complex.instRing
attribute [instance] Complex.addCommGroup
attribute [instance] RCLike.toInnerProductSpaceReal
attribute [instance 2000] NormedSpace.complexToReal

""",
        "",
        "Mock2 Advanced remove obsolete reciprocal instance restoration",
    )
    M2A.write_text(m2a, encoding="utf-8")

    fa = FA.read_text(encoding="utf-8")
    fa = replace_exact(
        fa,
        """  have hv' :
      ((v : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        (F * j ^ 2) * (v : SmoothQuotientCompactFunction) z := by
    have hFactor := inverseEtaPaperOrbitMultiplier_factor_add_one
      GammaTwo n γ z
    rw [hFactor] at hv0
    simpa [F, M, j, OrbitMultiplier, mul_assoc] using hv0
""",
        """  have hv' :
      ((v : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (((γ : GammaTwo) : SL(2, ℤ)) • z) =
        (F * j ^ 2) * (v : SmoothQuotientCompactFunction) z := by
    rw [fixedPhaseGreen_targetFactor_reindex n γ z] at hv0
    simpa [F, M, j, mul_assoc] using hv0
""",
        "FunctionalAnalysis reindex the exposed target factor directly",
    )
    fa = replace_exact(
        fa,
        """  have hp : (p : ℂ) = (a : ℂ) / 2 := by
    norm_num [p]
  rw [Complex.ofReal_mul, Complex.ofReal_div, hp]
  ring
""",
        """  rw [Complex.ofReal_mul, Complex.ofReal_div]
  ring
""",
        "FunctionalAnalysis remove the already-normalized exponent rewrite",
    )
    fa = replace_in_block(
        fa,
        "namespace FixedPhasePeterssonCoordinates",
        "end FixedPhasePeterssonCoordinates",
        "Complex.conj",
        "star",
        3,
        "FunctionalAnalysis use star throughout fixed-phase conjugation",
    )
    FA.write_text(fa, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
