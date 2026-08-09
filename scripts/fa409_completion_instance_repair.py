from pathlib import Path
import hashlib

path = Path('PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
text = path.read_text(encoding='utf-8')
expected = '5f2d7615aaad7bb3a232d19829f0f801278e7ab2fa2f66ccb68408b87647e620'
actual = hashlib.sha256(text.encode()).hexdigest()
if actual != expected:
    raise SystemExit(f'unexpected input sha256: {actual}')

repls = [
("""theorem norm_baseExtension_le_one : ‖Q.baseExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.baseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_baseExtension_le x

""",
"""theorem norm_baseExtension_le_one : ‖Q.baseExtension‖ ≤ 1 := by
  exact Q.baseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_baseExtension_le x

"""),
("""theorem norm_raiseExtension_le_one : ‖Q.raiseExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.raiseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_raiseExtension_le x

""",
"""theorem norm_raiseExtension_le_one : ‖Q.raiseExtension‖ ≤ 1 := by
  exact Q.raiseExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_raiseExtension_le x

"""),
("""theorem norm_lowerExtension_le_one : ‖Q.lowerExtension‖ ≤ 1 := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact Q.lowerExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_lowerExtension_le x

""",
"""theorem norm_lowerExtension_le_one : ‖Q.lowerExtension‖ ≤ 1 := by
  exact Q.lowerExtension.opNorm_le_bound zero_le_one fun x => by
    simpa only [one_mul] using Q.norm_lowerExtension_le x

"""),
("""noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion := by
  letI : NormedSpace ℂ Q.SobolevCompletion :=
    UniformSpace.Completion.instNormedSpace ℂ Q.GraphRange
  exact innerSLFlip ℂ

""",
"""noncomputable def completionEnergyOperator :
    WeakAntiOperator Q.SobolevCompletion :=
  innerSLFlip ℂ

"""),
("""@[simp]
theorem completionEnergyOperator_apply (u v : Q.SobolevCompletion) :
    Q.completionEnergyOperator u v = ⟪v, u⟫_ℂ :=
  innerSLFlip_apply_apply ℂ u v

""",
"""@[simp]
theorem completionEnergyOperator_apply (u v : Q.SobolevCompletion) :
    Q.completionEnergyOperator u v = ⟪v, u⟫_ℂ := by
  simpa [completionEnergyOperator] using
    (innerSLFlip_apply_apply ℂ u v)

"""),
("""theorem completionEnergyOperator_self_eq_zero_iff (u : Q.SobolevCompletion) :
    Q.completionEnergyOperator u u = 0 ↔ u = 0 := by
  rw [Q.completionEnergyOperator_apply, inner_self_eq_zero]

""",
"""theorem completionEnergyOperator_self_eq_zero_iff (u : Q.SobolevCompletion) :
    Q.completionEnergyOperator u u = 0 ↔ u = 0 := by
  rw [Q.completionEnergyOperator_apply]
  exact (inner_self_eq_zero (𝕜 := ℂ))

"""),
("""theorem completionEnergyOperator_coercive :
    ComplexLaxMilgram.ComplexCoerciveWith
      (V := Q.SobolevCompletion) 1 Q.completionEnergyOperator := by
  refine ⟨zero_lt_one, fun u ↦ ?_⟩
  rw [one_mul, Q.completionEnergyOperator_apply,
    inner_self_eq_norm_sq]

""",
"""theorem completionEnergyOperator_coercive :
    ComplexLaxMilgram.ComplexCoerciveWith
      (V := Q.SobolevCompletion) 1 Q.completionEnergyOperator := by
  refine ⟨zero_lt_one, fun u ↦ ?_⟩
  rw [one_mul, Q.completionEnergyOperator_apply]
  exact le_of_eq (norm_sq_eq_re_inner (𝕜 := ℂ) u)

"""),
("""theorem completionEnergyOperator_injective :
    Function.Injective Q.completionEnergyOperator :=
  FredholmBypass.coerciveForm_injective
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive

""",
"""theorem completionEnergyOperator_injective :
    Function.Injective Q.completionEnergyOperator :=
  FredholmBypass.coerciveForm_injective
    (V := Q.SobolevCompletion)
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive

"""),
("""theorem completionEnergyOperator_surjective :
    Function.Surjective Q.completionEnergyOperator :=
  FredholmBypass.coerciveForm_surjective
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive

""",
"""theorem completionEnergyOperator_surjective :
    Function.Surjective Q.completionEnergyOperator :=
  FredholmBypass.coerciveForm_surjective
    (V := Q.SobolevCompletion)
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive

"""),
("""noncomputable def completionEnergyEquiv :
    Q.SobolevCompletion ≃L[ℂ]
      StrongAntiDual Q.SobolevCompletion :=
  FredholmBypass.coerciveFormEquiv
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive

""",
"""noncomputable def completionEnergyEquiv :
    Q.SobolevCompletion ≃L[ℂ]
      StrongAntiDual Q.SobolevCompletion :=
  FredholmBypass.coerciveFormEquiv
    (V := Q.SobolevCompletion)
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive

"""),
("""@[simp]
theorem completionEnergyEquiv_apply (u : Q.SobolevCompletion) :
    Q.completionEnergyEquiv u = Q.completionEnergyOperator u :=
  rfl

""",
"""@[simp]
theorem completionEnergyEquiv_apply (u : Q.SobolevCompletion) :
    Q.completionEnergyEquiv u = Q.completionEnergyOperator u :=
  FredholmBypass.coerciveFormEquiv_apply
    (V := Q.SobolevCompletion)
    1 Q.completionEnergyOperator Q.completionEnergyOperator_coercive u

"""),
("""theorem completionEnergyOperator_solveCompletionEnergy
    (F : StrongAntiDual Q.SobolevCompletion) :
    Q.completionEnergyOperator (Q.solveCompletionEnergy F) = F := by
  change Q.completionEnergyEquiv
    (Q.completionEnergyEquiv.symm F) = F
  exact Q.completionEnergyEquiv.apply_symm_apply F

""",
"""theorem completionEnergyOperator_solveCompletionEnergy
    (F : StrongAntiDual Q.SobolevCompletion) :
    Q.completionEnergyOperator (Q.solveCompletionEnergy F) = F := by
  change Q.completionEnergyOperator
    (Q.completionEnergyEquiv.symm F) = F
  rw [← Q.completionEnergyEquiv_apply]
  exact Q.completionEnergyEquiv.apply_symm_apply F

"""),
("""theorem solveCompletionEnergy_norm_le
    (F : StrongAntiDual Q.SobolevCompletion) :
    ‖Q.solveCompletionEnergy F‖ ≤ ‖F‖ := by
  simpa [solveCompletionEnergy, completionEnergyEquiv] using
    (FredholmBypass.coerciveFormEquiv_symm_norm_le
      1 Q.completionEnergyOperator
      Q.completionEnergyOperator_coercive F)

""",
"""theorem solveCompletionEnergy_norm_le
    (F : StrongAntiDual Q.SobolevCompletion) :
    ‖Q.solveCompletionEnergy F‖ ≤ ‖F‖ := by
  simpa [solveCompletionEnergy] using
    (FredholmBypass.coerciveFormEquiv_symm_norm_le
      (V := Q.SobolevCompletion)
      1 Q.completionEnergyOperator
      Q.completionEnergyOperator_coercive F)

"""),
("""abbrev ClosedBaseDomain :=
  LinearMap.range Q.baseExtension.toLinearMap
""",
"""noncomputable abbrev ClosedBaseDomain :=
  LinearMap.range Q.baseExtension.toLinearMap
"""),
]

for i, (old, new) in enumerate(repls, 1):
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'replacement {i} expected once, found {count}')
    text = text.replace(old, new)

path.write_text(text, encoding='utf-8')
print('output_sha256=' + hashlib.sha256(text.encode()).hexdigest())
print('replacements=' + str(len(repls)))
