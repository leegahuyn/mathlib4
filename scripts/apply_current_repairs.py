from __future__ import annotations

import apply_sixty_seventh_pass_repairs as pass67
import apply_sixty_eighth_pass_repairs as pass68
import apply_sixty_ninth_pass_repairs as pass69
import apply_seventieth_pass_repairs as pass70
import apply_ninety_eighth_pass_repairs as pass98


def main() -> int:
    """Apply retained passes 67–70 and the current pass-98 repair chain."""
    pass67.main()
    pass68.main()
    pass69.main()
    pass70.main()
    return pass98.main()


if __name__ == "__main__":
    raise SystemExit(main())
