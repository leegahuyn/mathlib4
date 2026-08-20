from pathlib import Path
R = Path(__file__).resolve().parents[1]
M2 = R / "PrimalitySheafVerification/Mock2.lean"
M2A = R / "PrimalitySheafVerification/Mock2_Advanced.lean"
FA = R / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"

def rep(s, a, b, label, n=1):
    c = s.count(a)
    if c != n:
        raise RuntimeError(f"{label}: expected {n}, found {c}")
    print(f"{label}: applied {c}")
    return s.replace(a, b)

def main():
    s = M2.read_text()
    s = rep(s, '''  have hcompat : F.CompatibleFamily D sf := by
    intro i j
    have hij := hsf i j
    rw [toMathlibPresheaf_map_apply, toMathlibPresheaf_map_apply] at hij
    simpa only [D] using hij
  obtain ⟨s, hs, huniq⟩ := hF.existsUnique_gluing D sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    change F.res (le_iSup U i) s = sf i
    exact hs i
  · intro t ht
    apply huniq t
    intro i
    have hti := ht i
    rw [toMathlibPresheaf_map_apply] at hti
    change F.res (le_iSup U i) t = sf i
    exact hti
''', '''  have hcompat : F.CompatibleFamily D sf := by
    intro i j
    have hij := hsf i j
    change F.res ((U i).infLELeft (U j)) (sf i) =
      F.res ((U i).infLERight (U j)) (sf j) at hij
    exact hij
  obtain ⟨s, hs, huniq⟩ := hF.existsUnique_gluing D sf hcompat
  refine ⟨s, ?_, ?_⟩
  · intro i
    have hi := hs i
    change F.res (le_iSup U i) s = sf i at hi
    exact hi
  · intro t ht
    apply huniq t
    intro i
    have hti := ht i
    change F.res (le_iSup U i) t = sf i at hti
    exact hti
''', "Mock2 direct sheaf transport")
    s = rep(s, "(∞ : OnePoint ℝ)", "(⊤ : OnePoint ℝ)", "Mock2 OnePoint infinity syntax", 5)
    s = rep(s, '''@[simp] theorem scalarAnalyticData_totalOperator :
    scalarAnalyticData.totalOperator = 0 :=
  by
    ext u
    simp [AnalyticData.totalOperator, scalarAnalyticData]
''', '''@[simp] theorem scalarAnalyticData_totalOperator :
    scalarAnalyticData.totalOperator = 0 := by
  ext u
  change (0 : ℂ) + 0 = 0
  simp
''', "Mock2 scalar total operator")
    s = rep(s, '''def scalarSolution (z : ℂ) (r : RadiusBase) :
    Fibre scalarAnalyticData r :=
  ⟨⟨z, by simp [scalarAnalyticData]⟩, by
    rw [scalarAnalyticData_solutionSpace]
    trivial⟩
''', '''def scalarSolution (z : ℂ) (r : RadiusBase) :
    Fibre scalarAnalyticData r := by
  let u : scalarAnalyticData.domain :=
    ⟨z, by simp [scalarAnalyticData]⟩
  refine ⟨u, ?_⟩
  change u ∈ scalarAnalyticData.solutionSpace
  rw [scalarAnalyticData_solutionSpace]
  trivial
''', "Mock2 scalar solution carrier")
    s = rep(s, "abbrev TwoComponentSpace := ℂ × ℂ",
        "abbrev TwoComponentSpace := WithLp 2 (ℂ × ℂ)", "Mock2 Hilbert product carrier")
    s = rep(s, "toFun u := (u.1.1, 0)",
        "toFun u := WithLp.toLp 2 (u.1.ofLp.1, 0)", "Mock2 first coordinate value")
    s = rep(s, """  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp
""", """  map_add' x y := by
    apply WithLp.ofLp_injective 2
    ext <;> simp
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    ext <;> simp
""", "Mock2 first coordinate linearity")
    s = rep(s, "firstCoordinateOperator u = (u.1.1, 0)",
        "firstCoordinateOperator u = WithLp.toLp 2 (u.1.ofLp.1, 0)",
        "Mock2 first coordinate application")
    s = rep(s, "⟨(1, 0), by simp⟩", "⟨WithLp.toLp 2 (1, 0), by simp⟩",
        "Mock2 nonzero test vector")
    s = rep(s, "(fun z : TwoComponentSpace => z.1)",
        "(fun z : TwoComponentSpace => z.ofLp.1)", "Mock2 first projection")
    s = rep(s, "⟨⟨(0, 1), by simp [twoComponentAnalyticData]⟩, by",
        "⟨⟨WithLp.toLp 2 (0, 1), by simp [twoComponentAnalyticData]⟩, by",
        "Mock2 vertical solution")
    s = rep(s, "((u.1 : twoComponentAnalyticData.domain) : TwoComponentSpace).2)",
        "((u.1 : twoComponentAnalyticData.domain) : TwoComponentSpace).ofLp.2)",
        "Mock2 second projection")
    s = rep(s, '''  simpa [term, constantSeries] using
    (hasSum_ite_eq (0 : ℕ) c)
''', '''  convert (hasSum_ite_eq (0 : ℕ) c) using 1
  funext n
  by_cases h : n = 0
  · subst n
    simp [term, constantSeries]
  · simp [term, constantSeries, h]
''', "Mock2 constant one-term sum")
    s = rep(s, '''  simpa [term, monomialSeries] using
    (hasSum_ite_eq degree (c * q ^ degree))
''', '''  convert (hasSum_ite_eq degree (c * q ^ degree)) using 1
  funext n
  by_cases h : n = degree
  · subst n
    simp [term, monomialSeries]
  · simp [term, monomialSeries, h]
''', "Mock2 monomial one-term sum")
    s = rep(s, "  actual_certificate (X := Definition11.RadiusBase)\n    D A (identityActualFibreOperators D A)",
        "  actual_certificate D A (identityActualFibreOperators D A)",
        "Mock2 actual certificate arguments")
    s = rep(s, "    simp [unitKernel, unitSeriesTriple]",
        "    norm_num [unitKernel, unitSeriesTriple]", "Mock2 unit matching")
    s = rep(s, "    simp [unitKernel, degreeOneSeriesTriple]",
        "    norm_num [unitKernel, degreeOneSeriesTriple]", "Mock2 degree-one matching")
    M2.write_text(s)

    s = M2A.read_text()
    s = rep(s, "(u.2.2.add v.2.2)",
        "(MeasureTheory.MemLp.add u.2.2 v.2.2)", "Mock2 Advanced stored MemLp addition", 2)
    s = rep(s, "(u.2.2.const_smul c)",
        "(MeasureTheory.MemLp.const_smul u.2.2 c)", "Mock2 Advanced stored MemLp scalar", 2)
    s = rep(s, '''  section : GenuineAEAutomorphicSections.Section
  automorphic :
    GenuineAEAutomorphicSections.IsAutomorphicClass ν section
  squareIntegrable : IsPositiveFundamentalL2 section
''', '''  «section» : GenuineAEAutomorphicSections.Section
  automorphic :
    GenuineAEAutomorphicSections.IsAutomorphicClass ν «section»
  squareIntegrable : IsPositiveFundamentalL2 «section»
''', "Mock2 Advanced positive section field")
    s = rep(s, '''  section : GenuineInverseAEAutomorphicSections.Section
  automorphic :
    GenuineInverseAEAutomorphicSections.IsAutomorphicClass ν section
  squareIntegrable : IsInverseFundamentalL2 section
''', '''  «section» : GenuineInverseAEAutomorphicSections.Section
  automorphic :
    GenuineInverseAEAutomorphicSections.IsAutomorphicClass ν «section»
  squareIntegrable : IsInverseFundamentalL2 «section»
''', "Mock2 Advanced inverse section field")
    s = rep(s, "u.section", "u.«section»", "Mock2 Advanced section projections", 12)
    M2A.write_text(s)

    s = FA.read_text()
    s = rep(s, '''theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  have hs : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  simpa [inner_self_eq_norm_sq_to_K] using hs
''', '''theorem graphRange_re_inner_self_pos {x : Q.GraphRange} (hx : x ≠ 0) :
    0 < (⟪x, x⟫_ℂ).re := by
  calc
    0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    _ = (⟪x, x⟫_ℂ).re := norm_sq_eq_re_inner (𝕜 := ℂ) x
''', "FunctionalAnalysis graph positivity")
    s = rep(s, '''      change
        ‖(Q.graphExtension x).fst‖ ^ 2 +
            ‖(Q.graphExtension x).snd.fst‖ ^ 2 +
              ‖(Q.graphExtension x).snd.snd‖ ^ 2 =
          ‖(Q.graphExtension x).fst‖ ^ 2 +
            ‖(Q.graphExtension x).snd.fst‖ ^ 2 +
              ‖(Q.graphExtension x).snd.snd‖ ^ 2
      rfl
''', '''      change
        ‖(Q.graphExtension x).fst‖ ^ 2 +
          (‖(Q.graphExtension x).snd.fst‖ ^ 2 +
            ‖(Q.graphExtension x).snd.snd‖ ^ 2) =
        ‖(Q.graphExtension x).fst‖ ^ 2 +
          ‖(Q.graphExtension x).snd.fst‖ ^ 2 +
            ‖(Q.graphExtension x).snd.snd‖ ^ 2
      ring
''', "FunctionalAnalysis completed graph coordinates")
    FA.write_text(s)
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
