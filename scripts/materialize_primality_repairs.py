from __future__ import annotations

from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

SCRIPTS = [
    "apply_current_repairs.py",
    "apply_two_hundred_twenty_third_pass_repairs.py",
    "apply_two_hundred_twenty_fourth_pass_repairs.py",
    "apply_two_hundred_twenty_fifth_pass_repairs.py",
    "apply_two_hundred_twenty_sixth_pass_repairs.py",
    "apply_two_hundred_twenty_seventh_pass_repairs.py",
    "apply_two_hundred_twenty_eighth_pass_repairs.py",
    "apply_two_hundred_twenty_ninth_pass_repairs.py",
    "apply_two_hundred_thirtieth_pass_repairs.py",
    "apply_two_hundred_thirty_first_pass_repairs.py",
    "apply_two_hundred_thirty_second_pass_repairs.py",
    "apply_two_hundred_thirty_third_pass_repairs.py",
    "apply_two_hundred_thirty_fourth_pass_repairs.py",
    "apply_two_hundred_thirty_fifth_pass_repairs.py",
    "apply_two_hundred_thirty_sixth_pass_repairs.py",
    "apply_two_hundred_thirty_seventh_pass_repairs.py",
    "apply_two_hundred_thirty_eighth_pass_repairs.py",
    "apply_two_hundred_thirty_ninth_pass_repairs.py",
    "apply_two_hundred_fortieth_pass_repairs.py",
    "apply_two_hundred_forty_first_pass_repairs.py",
    "apply_two_hundred_forty_second_pass_repairs.py",
    "apply_two_hundred_forty_third_pass_repairs.py",
    "apply_two_hundred_forty_fourth_pass_repairs.py",
    "apply_two_hundred_forty_fifth_pass_repairs.py",
    "apply_two_hundred_forty_sixth_pass_repairs.py",
    "apply_two_hundred_forty_seventh_pass_repairs.py",
    "apply_two_hundred_forty_eighth_pass_repairs.py",
    "apply_two_hundred_forty_ninth_pass_repairs.py",
    "apply_two_hundred_fiftieth_pass_repairs.py",
    "apply_two_hundred_fifty_first_pass_repairs.py",
    "apply_two_hundred_fifty_second_pass_repairs.py",
    "apply_two_hundred_fifty_third_pass_repairs.py",
    "apply_two_hundred_fifty_fourth_pass_repairs.py",
    "apply_two_hundred_fifty_fifth_pass_repairs.py",
    "apply_two_hundred_fifty_sixth_pass_repairs.py",
    "apply_two_hundred_fifty_seventh_pass_repairs.py",
    "apply_two_hundred_fifty_eighth_pass_repairs.py",
    "apply_two_hundred_fifty_ninth_pass_repairs.py",
    "apply_two_hundred_sixtieth_pass_repairs.py",
    "apply_two_hundred_sixty_first_pass_repairs.py",
    "apply_two_hundred_sixty_second_pass_repairs.py",
    "apply_two_hundred_sixty_third_pass_repairs.py",
    "apply_two_hundred_sixty_fourth_pass_repairs.py",
    "apply_two_hundred_sixty_fifth_pass_repairs.py",
    "apply_two_hundred_sixty_sixth_pass_repairs.py",
    "apply_two_hundred_sixty_seventh_pass_repairs.py",
    "apply_two_hundred_sixty_eighth_pass_repairs.py",
    "apply_two_hundred_sixty_ninth_pass_repairs.py",
    "apply_two_hundred_seventieth_pass_repairs.py",
    "apply_two_hundred_seventy_first_pass_repairs.py",
    "apply_two_hundred_seventy_second_pass_repairs.py",
    "apply_two_hundred_seventy_third_pass_repairs.py",
    "apply_two_hundred_seventy_fourth_pass_repairs.py",
    "apply_two_hundred_seventy_fifth_pass_repairs.py",
    "apply_two_hundred_seventy_sixth_pass_repairs.py",
    "apply_two_hundred_seventy_seventh_pass_repairs.py",
    "apply_two_hundred_seventy_eighth_pass_repairs.py",
    "apply_two_hundred_seventy_ninth_pass_repairs.py",
    "apply_two_hundred_eightieth_pass_repairs.py",
    "apply_two_hundred_eighty_first_pass_repairs.py",
    "apply_two_hundred_eighty_second_pass_repairs.py",
    "apply_two_hundred_eighty_third_pass_repairs.py",
    "apply_two_hundred_eighty_fourth_pass_repairs.py",
]


def main() -> int:
    for script in SCRIPTS:
        print(f"materialize: {script}", flush=True)
        subprocess.run([sys.executable, str(ROOT / script)], check=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
