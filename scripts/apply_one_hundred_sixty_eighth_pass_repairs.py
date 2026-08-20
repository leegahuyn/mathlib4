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
        ("    { predicate_restriction_stable := fun hUV hA =>\n        hMC hUV hA\n",
         "    { predicate_restriction_stable := fun hUV {A} hA =>\n        hMC hUV hA\n", "bind the implicit q-gauge section"),
    ])
    edit(A, [
        ("  rw [Functor.map_zsmul, Functor.map_id]\n",
         "  rw [Functor.map_zsmul]\n  exact congrArg (fun f => (N : ℤ) • f)\n    ((cyclicTensorFunctor M).map_id (ModuleCat.of ℤ ℤ))\n",
         "finish tensor functor map of identity explicitly"),
        ("""  toFun x := ⟨x, by
    change N • (x : ZMod M) = 0
    change cyclicNsmulLinearMap N M x = 0 at x.property
    exact x.property⟩
  invFun x := ⟨x, by
    change cyclicNsmulLinearMap N M x = 0
    change N • (x : ZMod M) = 0 at x.property
    exact x.property⟩
""",
         """  toFun x := ⟨x, by
    have hx := x.property
    change cyclicNsmulLinearMap N M x = 0 at hx
    change N • (x : ZMod M) = 0
    exact hx⟩
  invFun x := ⟨x, by
    have hx := x.property
    change N • (x : ZMod M) = 0 at hx
    change cyclicNsmulLinearMap N M x = 0
    exact hx⟩
""", "use local kernel proof variables"),
    ])
    edit(F, [
        ("""  have hweight :
      star (physicalExponent a / heightC z) =
        physicalExponent a / heightC z := by
    simp only [star_div, conj_physicalExponent, conj_heightC]
""",
         """  have hweight :
      star (physicalExponent a / heightC z) =
        physicalExponent a / heightC z := by
    simp [physicalExponent, heightC]
""", "prove real-valued weight conjugation by definitions"),
    ])
    return 0

if __name__ == "__main__": raise SystemExit(main())
