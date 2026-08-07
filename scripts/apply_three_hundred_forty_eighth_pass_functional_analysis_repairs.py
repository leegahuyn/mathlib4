from __future__ import annotations

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "3f8e5343e30ab2ce324fbde38e21cdd4289b8faf527a04c8529f28b06e6012f0"
EXPECTED_OUTPUT_SHA256 = "6941bcd0685044b1903cf0f380a7dc0e03ecc4a76981a75d5e0f6395ca172ab0"


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass348] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass348 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    start_marker = "theorem submodule_adjoint_adjoint_eq_topologicalClosure"
    end_marker = "/-- Once a densely defined operator is closable"
    start = text.find(start_marker)
    end = text.find(end_marker, start)
    print(f"FunctionalAnalysis double-adjoint theorem bounds: start={start} end={end}")
    if start < 0 or end < 0:
        raise RuntimeError("could not locate the double-adjoint theorem block")
    old = text[start:end]
    if old.count("gᗮᗮ") != 2 or old.count("gᗮ") != 4:
        raise RuntimeError("unexpected orthogonal-notation shape in double-adjoint theorem")

    new = """theorem submodule_adjoint_adjoint_eq_topologicalClosure
    (g : Submodule ℂ (E × F)) :
    g.adjoint.adjoint = g.topologicalClosure := by
  calc
    g.adjoint.adjoint = g.orthogonal.orthogonal := by
      ext x
      rcases x with ⟨x₀, x₁⟩
      constructor
      · intro hx
        rw [Submodule.mem_orthogonal]
        rintro ⟨p, q⟩ hpq
        have hpqAdj : (q, -p) ∈ g.adjoint := by
          rw [Submodule.mem_adjoint_iff]
          intro a b hab
          have hOrth :=
            (Submodule.mem_orthogonal (K := g) (p, q)).mp hpq (a, b) hab
          simpa only [prod_inner_apply, inner_neg_right, sub_neg_eq_add,
            add_comm] using hOrth
        have hDouble :=
          (Submodule.mem_adjoint_iff g.adjoint (x₀, x₁)).mp hx q (-p) hpqAdj
        simp only [prod_inner_apply, inner_neg_left] at hDouble ⊢
        linear_combination -hDouble
      · intro hx
        rw [Submodule.mem_adjoint_iff]
        intro c d hcd
        have hOrth : (-d, c) ∈ g.orthogonal := by
          rw [Submodule.mem_orthogonal]
          rintro ⟨a, b⟩ hab
          have hAdj :=
            (Submodule.mem_adjoint_iff g (c, d)).mp hcd a b hab
          simpa only [prod_inner_apply, inner_neg_right] using hAdj
        have hDouble :=
          (Submodule.mem_orthogonal (K := g.orthogonal) (x₀, x₁)).mp
            hx (-d, c) hOrth
        simp only [prod_inner_apply, inner_neg_left] at hDouble
        linear_combination -hDouble
    _ = g.topologicalClosure := g.orthogonal_orthogonal_eq_closure

"""
    text = text[:start] + new + text[end:]

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass348 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(text, encoding="utf-8")
    print("[pass348] FunctionalAnalysis explicit complex orthogonal double-adjoint theorem repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
