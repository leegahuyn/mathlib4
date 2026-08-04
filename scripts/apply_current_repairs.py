from __future__ import annotations

from apply_fifty_fifth_pass_repairs import main as apply_fifty_fifth_pass


def main() -> int:
    """Apply only repairs not yet materialized into the checked-in Lean sources."""
    return apply_fifty_fifth_pass()


if __name__ == "__main__":
    raise SystemExit(main())
