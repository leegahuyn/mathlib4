from __future__ import annotations

import apply_sixty_first_pass_repairs as pass61


def main() -> int:
    """Apply only the next unmaterialized Lean repair wave."""
    return pass61.main()


if __name__ == "__main__":
    raise SystemExit(main())
