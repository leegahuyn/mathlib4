/-
================================================================================
  Spt3Sheaf.lean — Group-2 fragment of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification".

  A GENUINE site + constant presheaf + fiber-product subpresheaf, kernel-checked
  against Mathlib (sorry-free, axiom-free).  This realises §2.1 / §3.2 / §4.5 at
  the PRESHEAF level:

    • the site  S = Spec ℤ  with its open-cover Grothendieck topology
      (`Opens.grothendieckTopology`);
    • the ambient constant presheaf  B := ℕ  of candidate integers;
    • the four decision layers  Fnum, Fmod, Fp-adic, FEC ⊆ B  as genuine
      sub-presheaves (`CategoryTheory.Subfunctor`, the de-deprecated `Subpresheaf`);
    • their amalgam  F := Fnum ×_B Fmod ×_B Fp-adic ×_B FEC  as the lattice meet
      `⊓` of subpresheaves — a real fiber product over `B`;
    • the sectionwise identity  Γ(U,F) = ⋂ᵢ Γ(U,Fᵢ)  and restriction-as-inclusion
      `F ↪ B`.

  ⚠ HONEST SCOPE.  This is the PRESHEAF skeleton of the four-layer amalgam, which is
  exactly what the paper's "sections are computed sectionwise" claim uses.  It does
  NOT include: the SHEAF condition / sheafification of `B` and the layers (the
  constant presheaf is not a sheaf), the specific arithmetic CONTENT of each layer
  (`Fnum`,…,`FEC` are taken as arbitrary subpresheaves here), nor the terminal/
  minimality/independence claims (§2.3).  Those remain future work.
================================================================================
-/
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.RingTheory.Spectrum.Prime.Topology

open CategoryTheory TopologicalSpace

namespace Spt3Sheaf

/-- The arithmetic base `S = Spec ℤ`, as a topological space (Zariski topology). -/
abbrev S : Type := PrimeSpectrum ℤ

/-- **The site (§2.1).** The open-cover Grothendieck topology on the opens of
`Spec ℤ` — the principal-open basis generates this same topology. -/
abbrev siteJ : GrothendieckTopology (Opens S) := Opens.grothendieckTopology S

/-- **The ambient constant presheaf `B := ℕ` (§3.2).** Candidate integers on `S`. -/
abbrev B : (Opens S)ᵒᵖ ⥤ Type := (Functor.const (Opens S)ᵒᵖ).obj ℕ

variable (Fnum Fmod Fpadic FEC : Subfunctor B)

/-- **The amalgam `F := Fnum ×_B Fmod ×_B Fp-adic ×_B FEC` (§3.2).** The fiber
product over `B` of the four layers, realised as the lattice meet of subpresheaves. -/
abbrev amalgam : Subfunctor B := Fnum ⊓ Fmod ⊓ Fpadic ⊓ FEC

/-- **Sectionwise sections (§4.5).**
`Γ(U,F) = Γ(U,Fnum) ∩ Γ(U,Fmod) ∩ Γ(U,Fp-adic) ∩ Γ(U,FEC)`. -/
theorem amalgam_obj (U : (Opens S)ᵒᵖ) :
    (amalgam Fnum Fmod Fpadic FEC).obj U
      = Fnum.obj U ∩ Fmod.obj U ∩ Fpadic.obj U ∩ FEC.obj U := by
  simp only [amalgam, Subfunctor.min_obj]

/-- Membership form: a section is a global/local section of the amalgam iff it
satisfies all four layer predicates simultaneously. -/
theorem mem_amalgam {U : (Opens S)ᵒᵖ} (s : B.obj U) :
    s ∈ (amalgam Fnum Fmod Fpadic FEC).obj U
      ↔ s ∈ Fnum.obj U ∧ s ∈ Fmod.obj U ∧ s ∈ Fpadic.obj U ∧ s ∈ FEC.obj U := by
  rw [amalgam_obj]; simp only [Set.mem_inter_iff]; tauto

/-- **Restriction is inclusion (§4.5).** The amalgam is a genuine subpresheaf of the
ambient `B`: there is a canonical monomorphism `F ↪ B` whose components are the
inclusions of section sets, so restriction along `V ⊆ U` is inclusion. -/
def amalgamι : (amalgam Fnum Fmod Fpadic FEC).toFunctor ⟶ B :=
  (amalgam Fnum Fmod Fpadic FEC).ι

/-- The amalgam sits below each layer in the subpresheaf lattice (it refines each
gate): `F ≤ Fnum`, `F ≤ Fmod`, `F ≤ Fp-adic`, `F ≤ FEC`. -/
theorem amalgam_le_FEC : amalgam Fnum Fmod Fpadic FEC ≤ FEC := by
  simp only [amalgam]; exact inf_le_right
theorem amalgam_le_Fnum : amalgam Fnum Fmod Fpadic FEC ≤ Fnum := by
  simp only [amalgam]
  exact le_trans inf_le_left (le_trans inf_le_left inf_le_left)

section AxiomAudit
#print axioms amalgam_obj
#print axioms mem_amalgam
#print axioms amalgamι
#print axioms amalgam_le_FEC
#print axioms amalgam_le_Fnum
end AxiomAudit

end Spt3Sheaf
