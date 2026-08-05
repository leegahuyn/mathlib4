from __future__ import annotations

import apply_sixty_seventh_pass_repairs as pass67
import apply_sixty_eighth_pass_repairs as pass68
import apply_sixty_ninth_pass_repairs as pass69
import apply_seventieth_pass_repairs as pass70
import apply_one_hundred_forty_fourth_pass_repairs as pass144
import apply_one_hundred_forty_fifth_pass_repairs as pass145
import apply_one_hundred_forty_sixth_pass_repairs as pass146
import apply_one_hundred_forty_seventh_pass_repairs as pass147
import apply_one_hundred_forty_eighth_pass_repairs as pass148
import apply_one_hundred_forty_ninth_pass_repairs as pass149
import apply_one_hundred_fiftieth_pass_repairs as pass150
import apply_one_hundred_fifty_second_pass_repairs as pass152
import apply_one_hundred_fifty_fourth_pass_repairs as pass154
import apply_one_hundred_fifty_sixth_pass_repairs as pass156
import apply_one_hundred_fifty_seventh_pass_repairs as pass157
import apply_one_hundred_fifty_eighth_pass_repairs as pass158
import apply_one_hundred_fifty_ninth_pass_repairs as pass159
import apply_one_hundred_sixty_first_pass_repairs as pass161
import apply_one_hundred_sixty_second_pass_repairs as pass162
import apply_one_hundred_sixty_third_pass_repairs as pass163
import apply_one_hundred_sixty_fourth_pass_repairs as pass164
import apply_one_hundred_sixty_fifth_pass_repairs as pass165
import apply_one_hundred_sixty_sixth_pass_repairs as pass166
import apply_one_hundred_sixty_seventh_pass_repairs as pass167
import apply_one_hundred_sixty_eighth_pass_repairs as pass168


def main() -> int:
    """Apply retained passes 67–70 and the current pass-168 repair chain."""
    pass67.main(); pass68.main(); pass69.main(); pass70.main()
    for repair in (
        pass144.main, pass145.main, pass146.main, pass147.main,
        pass148.main, pass149.main, pass150.main, pass152.main,
        pass154.main, pass156.main, pass157.main, pass158.main,
        pass159.main, pass161.main, pass162.main, pass163.main,
        pass164.main, pass165.main, pass166.main, pass167.main,
        pass168.main,
    ):
        code = repair()
        if code != 0:
            return code
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
