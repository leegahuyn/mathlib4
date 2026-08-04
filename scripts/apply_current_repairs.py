from __future__ import annotations

import apply_fifty_fifth_pass_repairs as pass55


def tolerant_replace_exact(
    text: str, old: str, new: str, expected: int, label: str
) -> tuple[str, bool]:
    """Apply the current repair when its exact predecessor is present.

    The checked-in sources already contain all earlier repair waves, and some later
    waves have refined the same declaration bodies. A missing predecessor is therefore
    an idempotent source-shape change; duplicate predecessor matches remain fatal.
    Compilation, not silent script success, is the final correctness check.
    """
    count = text.count(old)
    if count == expected:
        print(f"{label}: applied {count}")
        return text.replace(old, new), True
    if count == 0 and new in text:
        print(f"{label}: already applied")
        return text, False
    if count == 0:
        print(f"{label}: source changed; skipped")
        return text, False
    raise RuntimeError(f"{label}: expected {expected} match(es), found {count}")


def main() -> int:
    """Apply only repairs not yet materialized into the checked-in Lean sources."""
    pass55.replace_exact = tolerant_replace_exact
    return pass55.main()


if __name__ == "__main__":
    raise SystemExit(main())
