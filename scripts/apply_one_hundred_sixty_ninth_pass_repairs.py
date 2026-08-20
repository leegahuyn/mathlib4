from pathlib import Path
import apply_seventy_first_pass_repairs as p

M = Path("PrimalitySheafVerification/Mock2.lean")
A = Path("PrimalitySheafVerification/Mock2_Advanced.lean")
F = Path("PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean")


def edit(path, edits):
    s = path.read_text(encoding="utf-8")
    for old, new, label in edits:
        s, _ = p.replace_exact(s, old, new, 1, label)
    path.write_text(s, encoding="utf-8", newline="\n")


def main():
    edit(M, [
        ("    { predicate_restriction_stable := fun hUV {A} hA =>\n        hMC hUV hA\n",
         "    { predicate_restriction_stable := fun {U V} hUV {A} hA =>\n        hMC hUV hA\n", "bind all implicit covariance parameters"),
        ("""/-- Curvature is the second covariant derivative in this elementary model. -/
def QCurvature (∇ : Aq.QConnection) (U : Open) (x : Aq.Field U) : Aq.Field U :=
  ∇.D U (∇.D U x)

theorem curvature_restrict (∇ : Aq.QConnection) {U V : Open} (hUV : U ≤ V)
    (x : Aq.Field V) :
    Aq.res hUV (Aq.QCurvature ∇ V x) =
      Aq.QCurvature ∇ U (Aq.res hUV x) := by
  calc
    Aq.res hUV (∇.D V (∇.D V x))
        = ∇.D U (Aq.res hUV (∇.D V x)) := ∇.restrict_D hUV (∇.D V x)
    _ = ∇.D U (∇.D U (Aq.res hUV x)) := by rw [∇.restrict_D hUV x]

/-- A gauge transformation compatible with restriction. -/
structure GaugeTransform where
  act : ∀ U : Open, Aq.Field U → Aq.Field U
  restrict_act :
    ∀ {U V : Open} (hUV : U ≤ V) (x : Aq.Field V),
      Aq.res hUV (act V x) = act U (Aq.res hUV x)

def GaugeCovariant (∇ : Aq.QConnection) (g : Aq.GaugeTransform) : Prop :=
  ∀ (U : Open) (x : Aq.Field U), ∇.D U (g.act U x) = g.act U (∇.D U x)

theorem gauge_covariance_formula {∇ : Aq.QConnection} {g : Aq.GaugeTransform}
    (hg : Aq.GaugeCovariant ∇ g) (U : Open) (x : Aq.Field U) :
    ∇.D U (g.act U x) = g.act U (∇.D U x) := hg U x

/-- Legacy fixed-point sector for the elementary second-derivative model.
This predicate is `QCurvature x = x`, not Definition 18's zero-curvature
sector.  The paper-faithful subtype is `Mock2.FlatSector` in §F.1.5. -/
def FlatSector (∇ : Aq.QConnection) (U : Open) (x : Aq.Field U) : Prop :=
  Aq.QCurvature ∇ U x = x

/-- Legacy assumption-packaging for the fixed-point sector above.  Its
vanishing fields assume the conclusion directly and are not the order-theoretic
proof of Proposition 19; use `Proposition19Hypotheses` and
`proposition19_M_and_R_vanish` for that result. -/
structure EffectiveMassFunctional (∇ : Aq.QConnection) where
  mass : ∀ U : Open, Aq.Field U → ℕ
  potential : ∀ U : Open, Aq.Field U → ℕ
  mass_vanishes_on_flat :
    ∀ {U : Open} {x : Aq.Field U}, Aq.FlatSector ∇ U x → mass U x = 0
  potential_vanishes_on_flat :
    ∀ {U : Open} {x : Aq.Field U}, Aq.FlatSector ∇ U x → potential U x = 0

theorem flat_sector_mass_vanishes {∇ : Aq.QConnection}
    (E : Aq.EffectiveMassFunctional ∇) {U : Open} {x : Aq.Field U}
    (hflat : Aq.FlatSector ∇ U x) :
    E.mass U x = 0 := E.mass_vanishes_on_flat hflat

theorem flat_sector_potential_vanishes {∇ : Aq.QConnection}
    (E : Aq.EffectiveMassFunctional ∇) {U : Open} {x : Aq.Field U}
    (hflat : Aq.FlatSector ∇ U x) :
    E.potential U x = 0 := E.potential_vanishes_on_flat hflat
""",
         """/-- Curvature is the second covariant derivative in this elementary model. -/
def QCurvature (nabla : Aq.QConnection) (U : Open) (x : Aq.Field U) : Aq.Field U :=
  nabla.D U (nabla.D U x)

theorem curvature_restrict (nabla : Aq.QConnection) {U V : Open} (hUV : U ≤ V)
    (x : Aq.Field V) :
    Aq.res hUV (Aq.QCurvature nabla V x) =
      Aq.QCurvature nabla U (Aq.res hUV x) := by
  calc
    Aq.res hUV (nabla.D V (nabla.D V x))
        = nabla.D U (Aq.res hUV (nabla.D V x)) :=
          nabla.restrict_D hUV (nabla.D V x)
    _ = nabla.D U (nabla.D U (Aq.res hUV x)) := by
      rw [nabla.restrict_D hUV x]

/-- A gauge transformation compatible with restriction. -/
structure GaugeTransform where
  act : ∀ U : Open, Aq.Field U → Aq.Field U
  restrict_act :
    ∀ {U V : Open} (hUV : U ≤ V) (x : Aq.Field V),
      Aq.res hUV (act V x) = act U (Aq.res hUV x)

def GaugeCovariant (nabla : Aq.QConnection) (g : Aq.GaugeTransform) : Prop :=
  ∀ (U : Open) (x : Aq.Field U),
    nabla.D U (g.act U x) = g.act U (nabla.D U x)

theorem gauge_covariance_formula {nabla : Aq.QConnection} {g : Aq.GaugeTransform}
    (hg : Aq.GaugeCovariant nabla g) (U : Open) (x : Aq.Field U) :
    nabla.D U (g.act U x) = g.act U (nabla.D U x) := hg U x

/-- Legacy fixed-point sector for the elementary second-derivative model.
This predicate is `QCurvature x = x`, not Definition 18's zero-curvature
sector.  The paper-faithful subtype is `Mock2.FlatSector` in §F.1.5. -/
def FlatSector (nabla : Aq.QConnection) (U : Open) (x : Aq.Field U) : Prop :=
  Aq.QCurvature nabla U x = x

/-- Legacy assumption-packaging for the fixed-point sector above.  Its
vanishing fields assume the conclusion directly and are not the order-theoretic
proof of Proposition 19; use `Proposition19Hypotheses` and
`proposition19_M_and_R_vanish` for that result. -/
structure EffectiveMassFunctional (nabla : Aq.QConnection) where
  mass : ∀ U : Open, Aq.Field U → ℕ
  potential : ∀ U : Open, Aq.Field U → ℕ
  mass_vanishes_on_flat :
    ∀ {U : Open} {x : Aq.Field U}, Aq.FlatSector nabla U x → mass U x = 0
  potential_vanishes_on_flat :
    ∀ {U : Open} {x : Aq.Field U}, Aq.FlatSector nabla U x → potential U x = 0

theorem flat_sector_mass_vanishes {nabla : Aq.QConnection}
    (E : Aq.EffectiveMassFunctional nabla) {U : Open} {x : Aq.Field U}
    (hflat : Aq.FlatSector nabla U x) :
    E.mass U x = 0 := E.mass_vanishes_on_flat hflat

theorem flat_sector_potential_vanishes {nabla : Aq.QConnection}
    (E : Aq.EffectiveMassFunctional nabla) {U : Open} {x : Aq.Field U}
    (hflat : Aq.FlatSector nabla U x) :
    E.potential U x = 0 := E.potential_vanishes_on_flat hflat
""", "rename reserved nabla binders"),
    ])
    edit(A, [
        ("""@[simp]
theorem integral_unitIntervalDensity :
    (∫ x : ℝ, unitIntervalDensity x) = 1 := by
  rw [unitIntervalDensity, integral_indicator measurableSet_Ioc]
  simp [Real.volume_Ioc]
""",
         """@[simp]
theorem integral_unitIntervalDensity :
    (∫ x : ℝ, unitIntervalDensity x) = 1 := by
  change (∫ x : ℝ, (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) = 1
  rw [integral_indicator measurableSet_Ioc]
  simp [Real.volume_Ioc]
""", "expose unit interval density under the integral"),
        ("""@[simp]
theorem integral_stageTest (T : ℝ) (hT : 0 < T) (n : ℕ) :
    (∫ t : ℝ, stageTest T hT n t) =
      ∫ t in Icc (-(n : ℝ)) (n : ℝ), smoothTest T hT t := by
  rw [stageTest, integral_indicator measurableSet_Icc]
""",
         """@[simp]
theorem integral_stageTest (T : ℝ) (hT : 0 < T) (n : ℕ) :
    (∫ t : ℝ, stageTest T hT n t) =
      ∫ t in Icc (-(n : ℝ)) (n : ℝ), smoothTest T hT t := by
  change
    (∫ t : ℝ, (Icc (-(n : ℝ)) (n : ℝ)).indicator
      (smoothTest T hT) t) = _
  rw [integral_indicator measurableSet_Icc]
""", "expose the stage indicator under the integral"),
    ])
    edit(F, [
        ("  simpa [inverseEtaPaperOrbitMultiplier] using\n    inverseEtaHalfOrbitMultiplier_factor Γ n γ z\n",
         "  simpa only [inverseEtaPaperOrbitMultiplier, neg_paperOrbitExponent] using\n    inverseEtaHalfOrbitMultiplier_factor Γ n γ z\n", "restrict factor transport simplification"),
        ("  simpa [inverseEtaPaperOrbitMultiplier] using\n    inverseEtaHalfOrbitMultiplier_factor_add_one Γ n γ z\n",
         "  simpa only [inverseEtaPaperOrbitMultiplier, neg_paperOrbitExponent] using\n    inverseEtaHalfOrbitMultiplier_factor_add_one Γ n γ z\n", "restrict shifted factor simplification"),
        ("  change (inverseEtaHalfOrbitMultiplier Γ n).nu γ =\n    (inverseEtaMultiplier Γ).nu γ\n  rfl\n",
         "  simpa only [inverseEtaPaperOrbitMultiplier, neg_paperOrbitExponent]\n", "transport the eta phase through the exponent equality"),
        ("abbrev InverseEtaPaperOrbitSection\n",
         "noncomputable abbrev InverseEtaPaperOrbitSection\n", "mark the orbit section abbreviation noncomputable"),
    ])
    return 0

if __name__ == "__main__": raise SystemExit(main())
