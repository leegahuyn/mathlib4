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
import apply_one_hundred_sixty_ninth_pass_repairs as pass169
import apply_one_hundred_seventieth_pass_repairs as pass170
import apply_one_hundred_seventy_first_pass_repairs as pass171
import apply_one_hundred_seventy_second_pass_repairs as pass172
import apply_one_hundred_seventy_third_pass_repairs as pass173
import apply_one_hundred_seventy_fourth_pass_repairs as pass174
import apply_one_hundred_seventy_fifth_pass_repairs as pass175
import apply_one_hundred_seventy_sixth_pass_repairs as pass176
import apply_one_hundred_seventy_seventh_pass_repairs as pass177
import apply_one_hundred_seventy_eighth_pass_repairs as pass178
import apply_one_hundred_seventy_ninth_pass_repairs as pass179
import apply_one_hundred_eightieth_pass_repairs as pass180


def main() -> int:
    """Apply retained passes 67–70 and the current pass-180 repair chain."""
    pass67.main(); pass68.main(); pass69.main(); pass70.main()
    for repair in (
        pass144.main, pass145.main, pass146.main, pass147.main,
        pass148.main, pass149.main, pass150.main, pass152.main,
        pass154.main, pass156.main, pass157.main, pass158.main,
        pass159.main, pass161.main, pass162.main, pass163.main,
        pass164.main, pass165.main, pass166.main, pass167.main,
        pass168.main, pass169.main, pass170.main, pass171.main,
        pass172.main, pass173.main, pass174.main, pass175.main,
        pass176.main, pass177.main, pass178.main, pass179.main,
        pass180.main,
    ):
        code = repair()
        if code != 0:
            return code
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
