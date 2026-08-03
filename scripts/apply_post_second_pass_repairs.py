from __future__ import annotations

from apply_mock1_advanced_membership_repairs import main as repair_mock1_advanced_memberships
from apply_spt2_canonical_final import main as repair_spt2_canonical


def main() -> int:
    repair_spt2_canonical()
    repair_mock1_advanced_memberships()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
