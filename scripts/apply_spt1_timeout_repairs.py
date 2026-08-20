from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Spt1.lean")


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count == 1:
        print(f"APPLIED: {label}")
        return text.replace(old, new, 1)
    if count == 0 and text.count(new) == 1:
        print(f"ALREADY APPLIED: {label}")
        return text
    raise RuntimeError(
        f"{label}: expected exactly one old or one new occurrence; "
        f"old={count}, new={text.count(new)}"
    )


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    original = text

    text = replace_once(
        text,
        "theorem resC_proj (N : ℕ) (n : ℕ) : Projective ((resC N).X n) := by\n",
        "set_option maxHeartbeats 800000 in\n"
        "theorem resC_proj (N : ℕ) (n : ℕ) : Projective ((resC N).X n) := by\n",
        "give typeclass normalization enough heartbeats in resC_proj",
    )

    text = replace_once(
        text,
        "      have h2 : (p : ℝ) ^ padicValNat p n ≤ (p : ℝ) ^ (n - 1) := by\n"
        "        gcongr\n"
        "        exact hp1\n",
        "      have h2 : (p : ℝ) ^ padicValNat p n ≤ (p : ℝ) ^ (n - 1) := by\n"
        "        gcongr\n",
        "remove a tactic executed after gcongr already closed the goal",
    )

    if text != original:
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print(f"Updated {PATH}")
    else:
        print("No changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
