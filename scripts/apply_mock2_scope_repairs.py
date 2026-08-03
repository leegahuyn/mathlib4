from __future__ import annotations

from pathlib import Path

PATH = Path("PrimalitySheafVerification/Mock2.lean")

INCLUDES = {
    "M_pos_of_setup": "hM", "M_ne_zero_of_setup": "hM",
    "k_pos_of_setup": "hk", "k_ne_zero_of_setup": "hk",
    "p_pos_of_prime": "hp", "p_ne_zero_of_prime": "hp",
    "padicExponentProxy_eq_padicValNat": "hp",
    "p_pow_dvd_M_iff_le_padicExponentProxy": "hM hp",
    "p_pow_dvd_M_iff_le_padicValNat": "hM hp",
    "Pk_pos": "hp", "Pk_ne_zero": "hp", "Pk_one_le": "hp",
    "p_dvd_Pk": "hk", "Pk_factorization": "hp",
    "Pk_factorization_self": "hp", "prime_pow_factorization_ne": "hp",
    "Pk_factorization_ne": "hp", "Pk_factorization_apply": "hp",
    "gcd_M_Pk_ne_zero": "hM", "gcd_M_Pk_pos": "hM",
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


def main() -> int:
    lines = PATH.read_text(encoding="utf-8").splitlines()
    changed = False
    for name, variables in INCLUDES.items():
        theorem_index = next((i for i, line in enumerate(lines)
            if line.startswith(f"theorem {name}") or line.startswith(f"lemma {name}")), None)
        if theorem_index is None:
            print(f"Mock2 {name}: source changed")
            continue
        if theorem_index > 0 and lines[theorem_index - 1].startswith("include "):
            continue
        insert_at = theorem_index
        j = theorem_index - 1
        while j >= 0 and not lines[j].strip():
            j -= 1
        if j >= 0 and lines[j].strip().endswith("-/"):
            while j >= 0 and not lines[j].lstrip().startswith("/--"):
                j -= 1
            if j >= 0:
                insert_at = j
        lines.insert(insert_at, f"include {variables} in")
        print(f"Mock2 {name}: included {variables}")
        changed = True

    text = "\n".join(lines) + "\n"
    text = text.replace("exact Nat.pow_pos (p_pos_of_prime p hp) k",
                        "exact Nat.pow_pos (p_pos_of_prime p hp)")
    if changed:
        PATH.write_text(text, encoding="utf-8", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
