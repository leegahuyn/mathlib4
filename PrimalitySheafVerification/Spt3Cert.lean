/-
================================================================================
  Spt3Cert.lean — Group-4 fragment (the EC/AKS completeness layer) of

      Lee Ga Hyun, "A Primality Sheaf and Global Certification".

  Theorem 18's hard `(⇐)` direction needs the EC/AKS layer `FEC` to be a SOUND +
  COMPLETE primality certificate.  Mathlib has NO AKS and NO ECPP.  But it DOES have
  the Lucas–Pratt certificate (`lucas_primality_iff`), which is genuinely sound and
  complete.  We use it as a concrete, fully-proved stand-in for `FEC` to show that
  the §5 global-section certification provably CLOSES once `FEC` is any sound+complete
  certificate — and we name the missing AKS input precisely.

  sorry-free, axiom-free.

  ⚠ HONEST SCOPE.  `LucasCert` is NOT the paper's EC/AKS gate; it is a different
  (also complete) certificate that Mathlib actually proves.  Replacing it by a real
  formalized AKS is the open problem `AKSIsComplete` named below.
================================================================================
-/
import Mathlib.NumberTheory.LucasPrimality

namespace Spt3Cert

/-- The Lucas–Pratt certificate predicate, used as a concrete sound+complete `FEC`. -/
def LucasCert (p : ℕ) : Prop :=
  ∃ a : ZMod p, a ^ (p - 1) = 1 ∧ ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1

/-- **Soundness** of the Lucas layer: a certificate forces primality. -/
theorem LucasCert_sound {p : ℕ} (h : LucasCert p) : p.Prime :=
  (lucas_primality_iff p).mpr h

/-- **Completeness** of the Lucas layer: every prime carries a certificate.  This is
exactly the deep `Hcomplete` the paper ASSUMES for EC/AKS — here it is a THEOREM. -/
theorem LucasCert_complete {p : ℕ} (h : p.Prime) : LucasCert p :=
  (lucas_primality_iff p).mp h

/-- **Certification, instantiated and UNCONDITIONALLY proved.** With the three
elementary layers trivial and `FEC := LucasCert`, the global-section certification
"prime ⇔ ∃ section" holds with BOTH directions proved, because the Lucas/Pratt
certificate is a genuine sound+complete primality certificate.  This is the honest
realisation of Theorem 18's architecture with a real (non-AKS) complete layer. -/
theorem prime_iff_section (X : ℕ) :
    X.Prime ↔ (True ∧ True ∧ True ∧ LucasCert X) :=
  ⟨fun h => ⟨trivial, trivial, trivial, LucasCert_complete h⟩,
   fun ⟨_, _, _, h⟩ => LucasCert_sound h⟩

/-- The single missing input for the paper's own layer, named as a Prop (NOT proved):
"a formalized AKS gate is a sound+complete primality certificate". -/
def AKSIsComplete (FEC_AKS : ℕ → Prop) : Prop := ∀ X, X.Prime ↔ FEC_AKS X

/-- Given ANY sound+complete layer (e.g. a future formalized AKS satisfying
`AKSIsComplete`), the certification closes.  This isolates the exact deep input. -/
theorem prime_iff_section_of_complete (FEC : ℕ → Prop)
    (hFEC : AKSIsComplete FEC) (X : ℕ) : X.Prime ↔ FEC X := hFEC X

section AxiomAudit
#print axioms LucasCert_sound
#print axioms LucasCert_complete
#print axioms prime_iff_section
#print axioms prime_iff_section_of_complete
end AxiomAudit

end Spt3Cert
