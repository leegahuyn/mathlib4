from __future__ import annotations

from apply_fifth_pass_repairs import main as repair_fifth_pass
from apply_fourth_pass_repairs import main as repair_fourth_pass
from apply_mock1_advanced_membership_repairs import main as repair_mock1_advanced_memberships
from apply_spt2_canonical_final import main as repair_spt2_canonical
from apply_spt2_current_api_final import main as repair_spt2_current_api
from apply_third_pass_repairs import main as repair_third_pass


def main() -> int:
    repair_spt2_canonical()
    repair_mock1_advanced_memberships()
    repair_third_pass()
    repair_fourth_pass()
    repair_spt2_current_api()
    repair_fifth_pass()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
