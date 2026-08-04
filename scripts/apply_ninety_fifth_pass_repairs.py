from __future__ import annotations

import apply_ninety_third_pass_repairs as pass93


def main() -> int:
    """Run the corrected pass-93 chain without the stale pass-94 rewrites."""
    return pass93.main()


if __name__ == "__main__":
    raise SystemExit(main())
