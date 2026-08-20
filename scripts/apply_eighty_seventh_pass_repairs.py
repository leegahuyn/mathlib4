from __future__ import annotations

import apply_eighty_third_pass_repairs as pass83


def main() -> int:
    """Run the corrected pass-83 repair set without the duplicate pass-84/85/86 chain."""
    return pass83.main()


if __name__ == "__main__":
    raise SystemExit(main())
