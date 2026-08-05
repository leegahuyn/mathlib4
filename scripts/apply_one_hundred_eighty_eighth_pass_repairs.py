from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M2 = ROOT / "PrimalitySheafVerification" / "Mock2.lean"


def replace_exact(text: str, old: str, new: str, label: str, expected: int = 1) -> str:
    count = text.count(old)
    if count != expected:
        raise RuntimeError(f"{label}: expected exactly {expected} match(es), found {count}")
    print(f"{label}: applied {expected}")
    return text.replace(old, new, expected)


def main() -> int:
    text = M2.read_text(encoding="utf-8")
    text = replace_exact(
        text,
        """          have hmap : map₁ = map₂ := by
            funext r s γ
            apply LinearEquiv.ext
            intro u
            exact h (r := r) (s := s) γ u
""",
        """          have hmap :
              (fun {r s : RadiusBase} (γ : RadiusPathClass r s) => map₁ γ) =
              (fun {r s : RadiusBase} (γ : RadiusPathClass r s) => map₂ γ) := by
            funext r s γ
            apply LinearEquiv.ext
            intro u
            exact h (r := r) (s := s) γ u
""",
        "Mock2 eta-expand dependent flat-transport maps in extensionality",
    )
    M2.write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
