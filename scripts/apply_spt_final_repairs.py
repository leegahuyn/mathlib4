from __future__ import annotations

from pathlib import Path

ROOT = Path("PrimalitySheafVerification")


def replace(path: Path, old: str, new: str, label: str) -> bool:
    text = path.read_text(encoding="utf-8")
    n = text.count(old)
    if n == 0:
        print(f"{label}: already applied/source changed")
        return False
    if n != 1:
        raise RuntimeError(f"{label}: expected one match, found {n}")
    path.write_text(text.replace(old, new), encoding="utf-8", newline="\n")
    print(f"{label}: applied")
    return True


def main() -> int:
    changed = False
    spt2 = ROOT / "Spt2.lean"
    changed |= replace(spt2,
"""  map_add' x y := rfl
  map_smul' r x := by
""",
"""  map_add' x y := by
    apply Algebra.Extension.Cotangent.ext
    rfl
  map_smul' r x := by
""", "Spt2 cotangent equivalence additivity")
    changed |= replace(spt2,
"""  unfold principalCotangentQuotEquiv quotientExtensionCotangentEquivKer
  rw [hmap]
""",
"""  unfold principalCotangentQuotEquiv quotientExtensionCotangentEquivKer
  rw [LinearEquiv.ofBijective_apply, hmap]
""", "Spt2 expose bijective equivalence application")

    spt3 = ROOT / "Spt3.lean"
    text = spt3.read_text(encoding="utf-8")
    n = text.count("leOfHom f.unop")
    if n:
        spt3.write_text(text.replace("leOfHom f.unop", "leOfHom f"), encoding="utf-8", newline="\n")
        print(f"Spt3 restriction arrow direction: applied {n}")
        changed = True

    spt4 = ROOT / "Spt4.lean"
    changed |= replace(spt4,
"""set_option maxHeartbeats 800000 in
theorem resC_d_succ_zero""",
"""theorem resC_d_succ_zero""", "Spt4 remove misplaced local option")

    print("Final SPT repairs changed sources." if changed else "No final SPT changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
