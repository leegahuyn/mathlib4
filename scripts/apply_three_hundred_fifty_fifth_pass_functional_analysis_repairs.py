from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "974545f05c6f2eaa981fd3ab3da37e61634c7a3db1088da1c10904e465ffbe47"
EXPECTED_OUTPUT_SHA256 = "a7e2a057912b21923979d7daf9f9ebaab90e0c1805c76c71b94e6cd15e700e1d"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    print(f"{label}: expected={expected} actual={count}")
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} occurrence(s), found {count}")
    return text.replace(old, new)


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass355] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass355 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    text = replace_exact(
        text,
        """    _ = 0 := by
      exact norm_zero
""",
        """    _ = 0 := by
      simpa using
        (norm_zero : ‖(0 : ContinuousSesquilinearForm H)‖ = 0)
""",
        "FunctionalAnalysis type the zero-form norm explicitly",
    )
    text = replace_exact(
        text,
        """  rw [hReal, ← mul_assoc, ← pow_two, hScale]
  ring
""",
        """  rw [hReal, ← mul_assoc, ← pow_two, hScale]
  rw [Complex.real_smul]
  ring
""",
        "FunctionalAnalysis identify the real scalar action",
    )
    text = replace_exact(
        text,
        """    rw [← dx_conj hf z, ← dy_conj hf z]
""",
        """    rw [dx_conj hf z, dy_conj hf z]
""",
        "FunctionalAnalysis orient conjugate derivative rewrites forward",
        expected=2,
    )
    text = replace_exact(
        text,
        """  all_goals try exact hf
  push_cast
  ring_nf
""",
        """  all_goals try exact hf
  simp only [smul_apply, smul_eq_mul]
  push_cast
  ring_nf
""",
        "FunctionalAnalysis expose scalar multiplication in the adjoint integrals",
        expected=2,
    )

    start_marker = "theorem submodule_adjoint_adjoint_eq_topologicalClosure"
    end_marker = "/-- Once a densely defined operator is closable"
    start = text.find(start_marker)
    end = text.find(end_marker, start)
    print(f"FunctionalAnalysis double-adjoint theorem bounds: start={start} end={end}")
    if start < 0 or end < 0:
        raise RuntimeError("could not locate the double-adjoint theorem block")
    new_double_adjoint = """theorem submodule_adjoint_adjoint_eq_topologicalClosure
    (g : Submodule ℂ (E × F)) :
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

"""
    text = text[:start] + new_double_adjoint + text[end:]

    text = replace_exact(
        text,
        """  · intro h x y
    simpa only [physicalRaise_apply, physicalLowerFromSucc_apply,
      l2Coordinate_l2CoreRangeEquiv_symm] using
        h ((l2CoreRangeEquiv n).symm x)
          ((l2CoreRangeEquiv (n + 1)).symm y)
""",
        """  · intro h x y
    change
      inner ℂ
          (raisedCoordinate n ((l2CoreRangeEquiv n).symm x))
          (y : OrbitPeterssonHilbert (n + 1)) +
        inner ℂ (x : OrbitPeterssonHilbert n)
          (lowerFromSuccCoordinate n
            ((l2CoreRangeEquiv (n + 1)).symm y)) = 0
    simpa only [l2Coordinate_l2CoreRangeEquiv_symm] using
      h ((l2CoreRangeEquiv n).symm x)
        ((l2CoreRangeEquiv (n + 1)).symm y)
""",
        "FunctionalAnalysis expose the physical Green coordinates",
    )
    text = replace_exact(
        text,
        "simpa only [← Submodule.topologicalClosure_coe] using",
        "simpa only [Submodule.topologicalClosure_coe] using",
        "FunctionalAnalysis orient closure coercions toward set closure",
        expected=5,
    )
    text = replace_exact(
        text,
        """    rw [← hzBase, ← hzValue]
    simpa only [physicalJointFromSucc_fst] using
      (physicalRaise (n + 1)).mem_graph z
""",
        """    rw [← hzBase, ← hzValue]
    change
      ((z : OrbitPeterssonHilbert (n + 1)),
        (physicalJointFromSucc n z).fst) ∈
          (physicalRaise (n + 1)).graph
    rw [physicalJointFromSucc_fst]
    exact (physicalRaise (n + 1)).mem_graph z
""",
        "FunctionalAnalysis expose the raising projection of the joint graph",
    )
    text = replace_exact(
        text,
        """    rw [← hzBase, ← hzValue]
    simpa only [physicalJointFromSucc_snd] using
      (physicalLowerFromSucc n).mem_graph z
""",
        """    rw [← hzBase, ← hzValue]
    change
      ((z : OrbitPeterssonHilbert (n + 1)),
        (physicalJointFromSucc n z).snd) ∈
          (physicalLowerFromSucc n).graph
    rw [physicalJointFromSucc_snd]
    exact (physicalLowerFromSucc n).mem_graph z
""",
        "FunctionalAnalysis expose the lowering projection of the joint graph",
    )
    text = replace_exact(
        text,
        """  have hMapped :
      unwrap (Q.graphExtension z) ∈ T.graph.topologicalClosure := by
    simpa only [Submodule.topologicalClosure_coe] using hMappedSet
""",
        """  have hMapped :
      unwrap (Q.graphExtension z) ∈ T.graph.topologicalClosure := by
    change unwrap (Q.graphExtension z) ∈
      closure (T.graph : Set (H₀ × WithLp 2 (HR × HL)))
    exact hMappedSet
""",
        "FunctionalAnalysis expose the generic graph closure as a set closure",
    )

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass355 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass355] FunctionalAnalysis first graph, closure, and adjoint frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
