from __future__ import annotations

import apply_sixty_third_pass_repairs as pass63


def main() -> int:
    """Apply only the next unmaterialized Lean repair wave."""
    return pass63.main()


if __name__ == "__main__":
    raise SystemExit(main())
