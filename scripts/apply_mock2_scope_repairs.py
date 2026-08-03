from __future__ import annotations

import re
from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock2.lean")


def main() -> int:
    text = PATH.read_text(encoding="utf-8")
    changed = False

    includes = {
        "M_pos_of_setup": "hM",
        "M_ne_zero_of_setup": "hM",
        "k_pos_of_setup": "hk",
        "k_ne_zero_of_setup": "hk",
        "p_pos_of_prime": "hp",
        "p_ne_zero_of_prime": "hp",
        "padicExponentProxy_eq_padicValNat": "hp",
        "p_pow_dvd_M_iff_le_padicExponentProxy": "hM hp",
        "p_pow_dvd_M_iff_le_padicValNat": "hM hp",
        "Pk_pos": "hp",
        "Pk_ne_zero": "hp",
        "Pk_one_le": "hp",
        "p_dvd_Pk": "hk",
        "Pk_factorization": "hp",
        "Pk_factorization_self": "hp",
        "prime_pow_factorization_ne": "hp",
        "Pk_factorization_ne": "hp",
        "Pk_factorization_apply": "hp",
        "gcd_M_Pk_ne_zero": "hM",
        "gcd_M_Pk_pos": "hM",
        "gcd_M_Pk_factorization_self": "hM hp",
        "gcd_M_Pk_factorization_ne": "hM hp",
        "gcd_M_Pk_factorization_apply": "hM hp",
        "gcd_M_Pk_factorization": "hM hp",
        "gcd_M_Pk_factorization_padicProxy": "hM hp",
        "gcd_M_Pk_factorization_padicValNat": "hM hp",
        "gcd_M_Pk_eq_pow_min_factorization": "hM hp",
        "gcd_M_Pk_eq_pow_min_padicProxy": "hM hp",
        "gcd_M_Pk_eq_pow_min_padicValNat": "hM hp",
        "gcd_M_Pk_eq_padicPart_of_padicValNat_le": "hM hp",
        "gcd_M_Pk_eq_Pk_of_k_le_padicValNat": "hM hp",
        "primePowerSetup_certificate": "hM hp hk",
    }

    for name, variables in includes.items():
        pattern = rf"(?m)^theorem {re.escape(name)}\b"
        replacement = f"include {variables} in\ntheorem {name}"
        text2, count = re.subn(pattern, replacement, text, count=1)
        if count == 0:
            print(f"Mock2 {name}: already included or source changed")
            continue
        print(f"Mock2 {name}: included {variables}")
        text = text2
        changed = True

    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
        print("Mock2 prime-power scope repairs changed source.")
    else:
        print("No Mock2 prime-power scope changes needed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
