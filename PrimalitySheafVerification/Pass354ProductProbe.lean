import Mathlib

open ComplexConjugate

#check @Submodule.mem_orthogonal
#check @Submodule.orthogonal_orthogonal_eq_closure
#check @Submodule.mem_adjoint_iff
#check @Prod.instNormedAddCommGroup
#check @Prod.instInnerProductSpace
#check @instInnerProductSpaceProd
#check @Prod.instModule

section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

#synth InnerProductSpace ℂ (E × F)
#synth CompleteSpace (E × F)

example (g : Submodule ℂ (E × F)) :
    g.orthogonal.orthogonal = g.topologicalClosure := by
  exact g.orthogonal_orthogonal_eq_closure

example (g : Submodule ℂ (E × F)) :
    gᗮᗮ = g.topologicalClosure := by
  exact Submodule.orthogonal_orthogonal_eq_closure g

example (g : Submodule ℂ (E × F)) :
    g.orthogonal.orthogonal = g.topologicalClosure := by
  change (gᗮ)ᗮ = g.topologicalClosure
  exact Submodule.orthogonal_orthogonal_eq_closure g

end
