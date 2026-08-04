from __future__ import annotations

import apply_sixty_second_pass_repairs as pass62


def main() -> int:
    """Apply only the next unmaterialized Lean repair wave."""
    return pass62.main()


if __name__ == "__main__":
    raise SystemExit(main())
