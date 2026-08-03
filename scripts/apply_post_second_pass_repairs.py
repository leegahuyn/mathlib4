from __future__ import annotations

from apply_eighth_pass_repairs import main as repair_eighth_pass
from apply_eleventh_pass_repairs import main as repair_eleventh_pass
from apply_fifth_pass_repairs import main as repair_fifth_pass
from apply_fourth_pass_repairs import main as repair_fourth_pass
from apply_mock1_advanced_fifth_repairs import main as repair_mock1_advanced_fifth
from apply_mock1_advanced_membership_repairs import main as repair_mock1_advanced_memberships
from apply_ninth_pass_repairs import main as repair_ninth_pass
from apply_seventh_pass_repairs import main as repair_seventh_pass
from apply_sixth_pass_repairs import main as repair_sixth_pass
from apply_spt2_canonical_final import main as repair_spt2_canonical
from apply_spt2_current_api_final import main as repair_spt2_current_api
from apply_tenth_pass_repairs import main as repair_tenth_pass
from apply_third_pass_repairs import main as repair_third_pass
from apply_twelfth_pass_repairs import main as repair_twelfth_pass


def main() -> int:
    repair_spt2_canonical()
    repair_mock1_advanced_memberships()
    repair_third_pass()
    repair_fourth_pass()
    repair_spt2_current_api()
    repair_fifth_pass()
    repair_mock1_advanced_fifth()
    repair_sixth_pass()
    repair_seventh_pass()
    repair_eighth_pass()
    repair_ninth_pass()
    repair_tenth_pass()
    repair_eleventh_pass()
    repair_twelfth_pass()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
