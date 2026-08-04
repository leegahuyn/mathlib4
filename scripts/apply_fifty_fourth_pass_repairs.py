from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace_exact(
    text: str, old: str, new: str, expected: int, label: str
) -> tuple[str, bool]:
    count = text.count(old)
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count != expected:
        raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")
    print(f"{label}: applied {count}")
    return text.replace(old, new), True


def nested_membership_body(name: str, alternatives: int) -> str:
    lines = [f"  simp only [{name}Requirements] at h"]
    for _ in range(alternatives):
        lines.append("  rcases h with rfl | h")
        lines.append("  · rfl")
    lines.append("  cases h")
    return "\n".join(lines) + "\n"


def repair_mock1_advanced() -> None:
    path = ROOT / "Mock1_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    specs = [
        ("objectSchema", 4),
        ("t1t5", 8),
        ("spt", 5),
        ("kernel", 8),
        ("exactCoefficient", 7),
        ("pAdic", 10),
        ("entropyRepro", 9),
        ("finalInstance", 3),
    ]
    for name, alternatives in specs:
        branches = " | ".join(["rfl"] * alternatives)
        old = f"""  simp only [{name}Requirements, List.mem_cons, List.mem_singleton] at h
  rcases h with {branches} <;> rfl
"""
        new = nested_membership_body(name, alternatives)
        text, did = replace_exact(
            text,
            old,
            new,
            2,
            f"Mock1Advanced destruct {name} membership one constructor at a time",
        )
        changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2() -> None:
    path = ROOT / "Mock2.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """        have hsrc :
            (p ^ shiftExponent M p k : ZMod (Pk p k)) *
                (z : ZMod (Pk p k)) =
              (((((p ^ shiftExponent M p k : ℕ) : ℤ) * z : ℤ)) :
                ZMod (Pk p k)) := by
          simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
"""
    new = """        have hsrc :
            (p ^ shiftExponent M p k : ZMod (Pk p k)) *
                (z : ZMod (Pk p k)) =
              (((((p ^ shiftExponent M p k : ℕ) : ℤ) * z : ℤ)) :
                ZMod (Pk p k)) := by
          ring_nf
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2 normalize the natural and integer casts in the source ring",
    )
    changed |= did

    old = """          _ =
              (p ^ shiftExponent M p k' : ZMod (Pk p k')) *
                ((((p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z : ℤ) :
                  ZMod (Pk p k')) := by
            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring
"""
    new = """          _ =
              (p ^ shiftExponent M p k' : ZMod (Pk p k')) *
                ((((p ^ (shiftExponent M p k - shiftExponent M p k') : ℕ) : ℤ) * z : ℤ) :
                  ZMod (Pk p k')) := by
            simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
            ring_nf
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2 normalize the reordered target factors after exponent splitting",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def repair_mock2_advanced() -> None:
    path = ROOT / "Mock2_Advanced.lean"
    text = path.read_text(encoding="utf-8")
    changed = False

    old = """  intro x hx
  exact AddSubmonoid.subset_closure hx
"""
    new = """  intro x hx
  exact M.core.le_topologicalClosure hx
"""
    text, did = replace_exact(
        text,
        old,
        new,
        2,
        "Mock2Advanced use the topological-submodule closure inclusion",
    )
    changed |= did

    old = """  have hstar :
      (starRingEnd ℂ) ((starRingEnd ℂ) (J.factor γ τ : ℂ)) =
        (J.factor γ τ : ℂ) := by
    simpa only [starRingEnd_apply] using
      (star_star (J.factor γ τ : ℂ))
  rw [hstar]
"""
    new = """  have hstar :
      (starRingEnd ℂ) ((starRingEnd ℂ) (J.factor γ τ : ℂ)) =
        (J.factor γ τ : ℂ) := by
    simpa only [starRingEnd_apply] using
      (star_star (J.factor γ τ : ℂ))
  have hstarInv := congrArg Inv.inv hstar
  rw [hstarInv]
"""
    text, did = replace_exact(
        text,
        old,
        new,
        1,
        "Mock2Advanced rewrite the inverse of the double conjugate explicitly",
    )
    changed |= did

    if changed:
        path.write_text(text, encoding="utf-8", newline="\n")


def main() -> int:
    repair_mock1_advanced()
    repair_mock2()
    repair_mock2_advanced()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
