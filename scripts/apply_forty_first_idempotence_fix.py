from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")
PASS41 = Path("scripts/apply_forty_first_pass_repairs.py")


def relax_pass41_zero_match_handling() -> bool:
    """Keep pass 41 strict on duplicate matches, but tolerate later source rewrites.

    The pass-41 replacements have already been materialized into the checked-in Lean
    sources. Later repair passes legitimately refine those exact proof bodies, so an
    absent old/new literal is an idempotent "source changed" case rather than a fatal
    error. Multiple matches remain fatal.
    """
    text = PASS41.read_text(encoding="utf-8")
    old = '''    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    raise RuntimeError(f"{label}: expected one match, found {count}")
'''
    new = '''    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count == 0:
        print(f"{label}: source changed; skipped")
        return text, False
    raise RuntimeError(f"{label}: expected one match, found {count}")
'''
    count = text.count(old)
    if count == 1:
        PASS41.write_text(text.replace(old, new, 1), encoding="utf-8", newline="\n")
        print("Pass 41 zero-match handling made idempotent")
        return True
    if count == 0 and new in text:
        print("Pass 41 zero-match handling already idempotent")
        return False
    raise RuntimeError(
        f"Pass 41 helper shape changed unexpectedly: expected one match, found {count}"
    )


def main() -> int:
    relax_pass41_zero_match_handling()

    text = PATH.read_text(encoding="utf-8")
    changed = False

    group_sizes = [
        ("objectSchemaRequirements", 4),
        ("t1t5Requirements", 8),
        ("sptRequirements", 5),
        ("kernelRequirements", 8),
        ("exactCoefficientRequirements", 7),
        ("pAdicRequirements", 10),
        ("entropyReproRequirements", 9),
        ("finalInstanceRequirements", 3),
    ]

    for group, size in group_sizes:
        old = f"  cases r <;> simp [{group}, sectionOf] at h ⊢\n"
        alternatives = " | ".join(["rfl"] * size)
        new = (
            f"  simp only [{group}, List.mem_cons, List.not_mem_nil, or_false] at h\n"
            f"  rcases h with {alternatives} <;> rfl\n"
        )
        count = text.count(old)
        if count:
            text = text.replace(old, new)
            changed = True
            print(f"Mock1Advanced {group}: normalized {count} remaining section map(s)")

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    else:
        print("Mock1Advanced section maps already normalized")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
