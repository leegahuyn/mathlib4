from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"


def once(text: str, old: str, new: str, label: str) -> str:
    a, b = text.count(old), text.count(new)
    print(f"{label}: old={a} new={b}")
    if a == 1 and b == 0:
        return text.replace(old, new)
    if a == 0 and b == 1:
        return text
    raise RuntimeError(f"{label}: expected one old or one new occurrence")


def main() -> int:
    s = TARGET.read_text(encoding="utf-8")
    edits = [
        ("  exact Q.baseExtension.opNorm_le_bound zero_le_one fun x => by\n    simpa only [one_mul] using Q.norm_baseExtension_le x\n",
         "  exact (Q.baseExtension : Q.SobolevCompletion →L[ℂ] H₀).opNorm_le_bound\n    zero_le_one fun x => by\n      rw [one_mul]\n      exact Q.norm_baseExtension_le x\n", "base operator norm"),
        ("  exact Q.raiseExtension.opNorm_le_bound zero_le_one fun x => by\n    simpa only [one_mul] using Q.norm_raiseExtension_le x\n",
         "  exact (Q.raiseExtension : Q.SobolevCompletion →L[ℂ] HR).opNorm_le_bound\n    zero_le_one fun x => by\n      rw [one_mul]\n      exact Q.norm_raiseExtension_le x\n", "raise operator norm"),
        ("  exact Q.lowerExtension.opNorm_le_bound zero_le_one fun x => by\n    simpa only [one_mul] using Q.norm_lowerExtension_le x\n",
         "  exact (Q.lowerExtension : Q.SobolevCompletion →L[ℂ] HL).opNorm_le_bound\n    zero_le_one fun x => by\n      rw [one_mul]\n      exact Q.norm_lowerExtension_le x\n", "lower operator norm"),
        ("  innerSLFlip ℂ\n\n@[simp]\ntheorem completionEnergyOperator_apply",
         "  (innerSLFlip ℂ :\n    Q.SobolevCompletion →L[ℂ] StrongAntiDual Q.SobolevCompletion)\n\n@[simp]\ntheorem completionEnergyOperator_apply", "energy operator type"),
        ("  FredholmBypass.coerciveForm_injective\n    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive\n",
         "  FredholmBypass.coerciveForm_injective\n    (V := Q.SobolevCompletion) 1 Q.completionEnergyOperator\n      Q.completionEnergyOperator_coercive\n", "injectivity space"),
        ("  FredholmBypass.coerciveForm_surjective\n    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive\n",
         "  FredholmBypass.coerciveForm_surjective\n    (V := Q.SobolevCompletion) 1 Q.completionEnergyOperator\n      Q.completionEnergyOperator_coercive\n", "surjectivity space"),
        ("  FredholmBypass.coerciveFormEquiv\n    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive\n",
         "  FredholmBypass.coerciveFormEquiv\n    (V := Q.SobolevCompletion) 1 Q.completionEnergyOperator\n      Q.completionEnergyOperator_coercive\n", "equivalence space"),
        ("  FredholmBypass.coerciveFormEquiv_apply\n    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive u\n",
         "  FredholmBypass.coerciveFormEquiv_apply\n    (V := Q.SobolevCompletion) 1 Q.completionEnergyOperator\n      Q.completionEnergyOperator_coercive u\n", "equivalence application space"),
        ("  simpa [solveCompletionEnergy, completionEnergyEquiv] using\n    (FredholmBypass.coerciveFormEquiv_symm_norm_le\n      1 Q.completionEnergyOperator\n      Q.completionEnergyOperator_coercive F)\n",
         "  change ‖Q.completionEnergyEquiv.symm F‖ ≤ ‖F‖\n  simpa [completionEnergyEquiv] using\n    (FredholmBypass.coerciveFormEquiv_symm_norm_le\n      (V := Q.SobolevCompletion) 1 Q.completionEnergyOperator\n      Q.completionEnergyOperator_coercive F)\n", "solution estimate"),
        ("  energyCompletionIsometry (graphRangeIsometry Qc Qs incl)\n\n/-- The two completions",
         "  (energyCompletionIsometry (graphRangeIsometry Qc Qs incl) :\n    Qc.SobolevCompletion →ₗᵢ[ℂ] Qs.SobolevCompletion)\n\n/-- The two completions", "completion inclusion type"),
        ("/-- `InverseEtaFixedPhaseCore` is an opaque noncomputable abbreviation of a\nsubmodule.  Re-export exactly the canonical subtype algebra structures at this\nboundary so the coordinate package does not invent a second module structure. -/\nnoncomputable local instance fixedPhaseCoreAddCommGroup (n : ℤ) :\n    AddCommGroup (InverseEtaFixedPhaseCore n) :=\n  inferInstanceAs\n    (AddCommGroup (inverseEtaFixedPhaseStableCoreSubmodule n))\n\nnoncomputable local instance fixedPhaseCoreModule (n : ℤ) :\n    Module ℂ (InverseEtaFixedPhaseCore n) :=\n  inferInstanceAs\n    (Module ℂ (inverseEtaFixedPhaseStableCoreSubmodule n))\n\n",
         "/-- Use the canonical subtype algebra structures of the fixed-phase submodule. -/\n\n", "recursive subtype instances"),
        ("  have hAction : g • z = gReal • z := by\n    apply UpperHalfPlane.ext\n    simp [gReal, UpperHalfPlane.coe_specialLinearGroup_apply]\n",
         "  have hAction : g • z = gReal • z := by\n    rfl\n", "integral modular action"),
        ("    (hDiff.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet)\n      .restrictScalars.contDiffOn_of_completeSpace\n",
         "    (hDiff.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet).restrictScalars.contDiffOn_of_completeSpace\n", "discriminant smooth syntax"),
        ("  · intro hz\n    refine ⟨z, ?_, rfl⟩\n    simpa only [Function.mem_support, quotientCoreCutoff_mk] using hz\n",
         "  · intro hz\n    refine ⟨z, ?_, rfl⟩\n    change quotientCoreCutoff (gammaTwoQuotientMk z) ≠ 0 at hz\n    rw [quotientCoreCutoff_mk] at hz\n    exact hz\n", "projected support converse"),
        ("    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw)\n      .differentiableWithinAt\n",
         "    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw).differentiableWithinAt\n", "eta differentiability syntax"),
        ("    (hEtaDiff.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet)\n      .restrictScalars.contDiffOn_of_completeSpace\n",
         "    (hEtaDiff.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet).restrictScalars.contDiffOn_of_completeSpace\n", "eta smooth syntax"),
        ("inverseEtaSection.covariance", "WeightSection.covariance inverseEtaSection", "inverse eta covariance", 4, 1),
        ("compactInverseEtaPaperCore.toSection", "SmoothCompactCore.toSection compactInverseEtaPaperCore", "paper core projection"),
        ("    (fun u : SmoothCompactCore inverseEtaPaperCertificate ↦\n      u.toSection UpperHalfPlane.I) hZero\n",
         "    (fun u : SmoothCompactCore inverseEtaPaperCertificate ↦\n      SmoothCompactCore.toSection u UpperHalfPlane.I) hZero\n", "paper core evaluation"),
        ("      u.toSection UpperHalfPlane.I) hZero\n  rw [SmoothCompactWeightCore.zero_apply]",
         "      SmoothCompactWeightCore.toSection u UpperHalfPlane.I) hZero\n  rw [SmoothCompactWeightCore.zero_apply]", "weight core evaluations", 2),
        ("  ⟨⟨(compactInverseEtaOrbitZeroWeightCore.toSection : ℍ → ℂ),\n      compactInverseEtaOrbitZeroWeightCore.realSmooth⟩,\n    compactInverseEtaOrbitZeroWeightCore.quotientCompact⟩\n",
         "  ⟨⟨(SmoothCompactWeightCore.toSection\n        compactInverseEtaOrbitZeroWeightCore : ℍ → ℂ),\n      SmoothCompactWeightCore.realSmooth\n        compactInverseEtaOrbitZeroWeightCore⟩,\n    SmoothCompactWeightCore.quotientCompact\n      compactInverseEtaOrbitZeroWeightCore⟩\n", "orbit zero quotient projections"),
        ("      compactInverseEtaOrbitZeroWeightCore.covariance γ z\n",
         "      SmoothCompactWeightCore.covariance\n        compactInverseEtaOrbitZeroWeightCore γ z\n", "orbit zero covariance"),
        ("  have hAction : ∀ x : ℍ, g • x = gReal • x := by\n    intro x\n    apply UpperHalfPlane.ext\n    simp [gReal, UpperHalfPlane.coe_specialLinearGroup_apply]\n",
         "  have hAction : ∀ x : ℍ, g • x = gReal • x := by\n    intro x\n    rfl\n", "modular metric action"),
    ]
    for edit in edits:
        old, new, label, *counts = edit
        expected_old = counts[0] if counts else 1
        existing_new = counts[1] if len(counts) > 1 else 0
        a, b = s.count(old), s.count(new)
        print(f"{label}: old={a} new={b}")
        if a == expected_old and b == existing_new:
            s = s.replace(old, new)
        elif a == 0 and b == existing_new + expected_old:
            pass
        else:
            raise RuntimeError(
                f"{label}: expected old/new {expected_old}/{existing_new} or "
                f"0/{existing_new + expected_old}, found {a}/{b}")
    TARGET.write_text(s, encoding="utf-8")
    print("[pass316] FunctionalAnalysis graph-completion and subtype API frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
