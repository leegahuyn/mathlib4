from __future__ import annotations

import apply_sixty_seventh_pass_repairs as pass67
import apply_sixty_eighth_pass_repairs as pass68
import apply_sixty_ninth_pass_repairs as pass69


def main() -> int:
    """Apply the retained repair chain and the next Lean repair wave."""
    pass67.main()
    pass68.main()
    return pass69.main()


if __name__ == "__main__":
    raise SystemExit(main())
