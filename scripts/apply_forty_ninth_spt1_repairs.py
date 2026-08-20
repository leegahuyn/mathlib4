from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Spt1.lean")


def replace_once(text: str, old: str, new: str, label: str) -> tuple[str, bool]:
    if new in text:
        print(f"{label}: already applied")
        return text, False
    count = text.count(old)
    if count == 0:
        # Earlier deterministic layers may already have rewritten the same
        # declaration with a different but sufficient local budget.  This
        # late compatibility layer must therefore be safely idempotent.
        print(f"{label}: already applied or source changed")
        return text, False
    if count != 1:
        raise RuntimeError(f"{label}: expected at most one match, found {count}")
    print(f"{label}: applied")
    return text.replace(old, new, 1), True


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    text, did_change = replace_once(
        text,
        "theorem resC_proj (U V W : C) (i : U ⟶ V) (j : V ⟶ W) :\n",
        "set_option maxHeartbeats 800000 in\n"
        "theorem resC_proj (U V W : C) (i : U ⟶ V) (j : V ⟶ W) :\n",
        "Spt1 resC_proj local heartbeat budget",
    )
    changed = changed or did_change

    text, did_change = replace_once(
        text,
        """    have h : 1 ≤ 415 * n := by
      have hp1 : 1 ≤ 415 := by norm_num
      gcongr
      exact hp1
""",
        """    have h : 1 ≤ 415 * n := by
      have hp1 : 1 ≤ 415 := by norm_num
      gcongr
""",
        "Spt1 remove tactic after gcongr closes the goal",
    )
    changed = changed or did_change

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    else:
        print("No source changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
