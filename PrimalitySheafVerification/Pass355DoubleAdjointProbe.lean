import Mathlib

open scoped ComplexConjugate

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

example (r : ℝ) (a b c : ℂ) :
    ((r : ℂ) * a) * b * c = r • (a * b * c) := by
  rw [Complex.real_smul]
  ring

example (j : ℂ) (m : ℕ) :
    (j ^ (2 : ℕ)) ^ m = j ^ ((2 : ℤ) * (m : ℤ)) := by
  calc
    (j ^ (2 : ℕ)) ^ m = j ^ (2 * m) := (pow_mul j 2 m).symm
    _ = j ^ ((2 : ℤ) * (m : ℤ)) := by
      rw [show (2 : ℤ) * (m : ℤ) = ((2 * m : ℕ) : ℤ) by omega]
      exact (zpow_ofNat j (2 * m)).symm

example (j : ℂ) (m : ℕ) :
    (j ^ (-2 : ℤ)) ^ (m + 1) =
      j ^ ((2 : ℤ) * Int.negSucc m) := by
  calc
    (j ^ (-2 : ℤ)) ^ (m + 1) =
        (j ^ (-2 : ℤ)) ^ (((m + 1 : ℕ) : ℤ)) := by
      exact (zpow_ofNat (j ^ (-2 : ℤ)) (m + 1)).symm
    _ = j ^ ((-2 : ℤ) * ((m + 1 : ℕ) : ℤ)) :=
      (zpow_mul j (-2 : ℤ) (((m + 1 : ℕ) : ℤ))).symm
    _ = j ^ ((2 : ℤ) * Int.negSucc m) := by
      congr 1 <;> omega

example (j y p : ℂ) (hj : j ≠ 0) :
    (y / (Complex.normSq j : ℂ)) ^ (2 : ℕ) *
        star (j ^ (2 : ℕ) * p) =
      j ^ (-2 : ℤ) * (y ^ (2 : ℕ) * star p) := by
  have hjc : star j ≠ 0 := by
    intro h
    apply hj
    have := congrArg star h
    simpa using this
  simp only [← starRingEnd_apply, map_mul, map_pow]
  rw [show (Complex.normSq j : ℂ) = star j * j by
    exact Complex.normSq_eq_conj_mul_self]
  simp only [zpow_negSucc, zpow_ofNat]
  field_simp [hj, hjc]
  <;> ring

example (g : Submodule ℂ (E × F)) :
    g.adjoint.adjoint = g.topologicalClosure := by
  let e : (E × F) ≃L[ℂ] WithLp 2 (E × F) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm
  let G : Submodule ℂ (WithLp 2 (E × F)) :=
    g.map e.toLinearMap
  apply Submodule.ext
  intro x
  rcases x with ⟨x₀, x₁⟩
  have hmem :
      (x₀, x₁) ∈ g.adjoint.adjoint ↔
        e (x₀, x₁) ∈ G.orthogonal.orthogonal := by
    constructor
    · intro hx
      rw [Submodule.mem_orthogonal]
      intro y hy
      have hAdj : (y.snd, -y.fst) ∈ g.adjoint := by
        rw [Submodule.mem_adjoint_iff]
        intro a b hab
        have hy0 : inner ℂ (e (a, b)) y = 0 :=
          (Submodule.mem_orthogonal G y).mp hy (e (a, b)) <| by
            exact ⟨(a, b), hab, rfl⟩
        simpa [e, WithLp.prod_inner_apply, inner_neg_right,
          sub_neg_eq_add, add_comm] using hy0
      have hDouble :=
        (Submodule.mem_adjoint_iff g.adjoint (x₀, x₁)).mp
          hx y.snd (-y.fst) hAdj
      simp only [e, WithLp.prodContinuousLinearEquiv_symm_apply,
        WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
        inner_neg_left] at hDouble ⊢
      linear_combination -hDouble
    · intro hx
      rw [Submodule.mem_adjoint_iff]
      intro c d hcd
      have hOrth : e (-d, c) ∈ G.orthogonal := by
        rw [Submodule.mem_orthogonal]
        intro y hy
        rcases hy with ⟨⟨a, b⟩, hab, rfl⟩
        have hAdj :=
          (Submodule.mem_adjoint_iff g (c, d)).mp hcd a b hab
        simpa [e, G, WithLp.prod_inner_apply, inner_neg_right,
          sub_eq_add_neg, add_comm] using hAdj
      have hDouble :=
        (Submodule.mem_orthogonal G.orthogonal (e (x₀, x₁))).mp
          hx (e (-d, c)) hOrth
      simp only [e, WithLp.prodContinuousLinearEquiv_symm_apply,
        WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
        inner_neg_left] at hDouble
      linear_combination -hDouble
  rw [hmem, G.orthogonal_orthogonal_eq_closure]
  change e (x₀, x₁) ∈ (G.topologicalClosure : Set _) ↔
    (x₀, x₁) ∈ (g.topologicalClosure : Set _)
  rw [Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe]
  change e (x₀, x₁) ∈ closure (e '' (g : Set (E × F))) ↔
    (x₀, x₁) ∈ closure (g : Set (E × F))
  rw [← e.image_closure]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = (x₀, x₁) := e.injective hxy
    simpa [this] using hy
  · intro hx
    exact ⟨(x₀, x₁), hx, rfl⟩
