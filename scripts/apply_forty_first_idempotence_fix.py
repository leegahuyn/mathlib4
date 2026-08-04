from __future__ import annotations

from pathlib import Path


PATH = Path("PrimalitySheafVerification/Mock1_Advanced.lean")


def main() -> int:
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
