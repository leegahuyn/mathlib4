#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

VARIANTS = {
    "gamma_revert_decide",
    "gamma_entry_coe",
    "gamma_entry_invexpl",
    "gamma_entry_solve",
    "gamma_membership_norm",
    "gamma_entry_simp_all",
}

HEADER = """theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
"""

CLASSIFY = """  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvS
  · exact hcentral
"""

ENTRY_FACTS = """  have h00 : ((gamma 0 0 : ℤ) : ZMod 2) = 1 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).1
  have h01 : ((gamma 0 1 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1
  have h10 : ((gamma 1 0 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1
  have h11 : ((gamma 1 1 : ℤ) : ZMod 2) = 1 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.2
"""

ENTRY_01_10 = """  have h01 : ((gamma 0 1 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1
  have h10 : ((gamma 1 0 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1
"""

SIMP_SET = """CongruenceSubgroup.Gamma_mem,
        Matrix.SpecialLinearGroup.SL2_inv_expl,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_fin_two,
        ModularGroup.S, ModularGroup.T"""

CASE_SPLIT = """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
"""

GAMMA_REVERT_DECIDE = HEADER + CLASSIFY + """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      exfalso
      revert hGamma
      decide
"""

GAMMA_ENTRY_COE = HEADER + ENTRY_FACTS + CLASSIFY + """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      norm_num [ModularGroup.coe_S, ModularGroup.coe_T,
        ModularGroup.coe_T_inv, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two] at h00 h01 h10 h11
"""

GAMMA_ENTRY_INVEXPL = HEADER + ENTRY_FACTS + CLASSIFY + """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      norm_num [ModularGroup.S, ModularGroup.T,
        Matrix.SpecialLinearGroup.SL2_inv_expl,
        Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
"""

GAMMA_ENTRY_SOLVE = HEADER + ENTRY_01_10 + CLASSIFY + CASE_SPLIT + f"""    all_goals
      exfalso
      solve
      | norm_num [{SIMP_SET}] at h01
      | norm_num [{SIMP_SET}] at h10
"""

GAMMA_MEMBERSHIP_NORM = HEADER + CLASSIFY + CASE_SPLIT + f"""    all_goals
      exfalso
      norm_num [{SIMP_SET}] at hGamma
"""

GAMMA_ENTRY_SIMP_ALL = HEADER + ENTRY_01_10 + CLASSIFY + CASE_SPLIT + f"""    all_goals
      exfalso
      simp_all only [{SIMP_SET}, Int.cast_neg, neg_eq_zero, one_ne_zero]
"""

PROOFS = {
    "gamma_revert_decide": GAMMA_REVERT_DECIDE,
    "gamma_entry_coe": GAMMA_ENTRY_COE,
    "gamma_entry_invexpl": GAMMA_ENTRY_INVEXPL,
    "gamma_entry_solve": GAMMA_ENTRY_SOLVE,
    "gamma_membership_norm": GAMMA_MEMBERSHIP_NORM,
    "gamma_entry_simp_all": GAMMA_ENTRY_SIMP_ALL,
}

DECL_RE = re.compile(
    r"(?ms)^theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\b.*?"
    r"(?=^/-! ## 2\.)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_probe43_gamma.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant: {variant}")

    path = Path(filename)
    before = path.read_bytes()
    text = before.decode("utf-8")
    matches = list(DECL_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected one gamma theorem, found {len(matches)}")
    m = matches[0]
    text = text[:m.start()] + PROOFS[variant] + "\n" + text[m.end():]
    path.write_text(text, encoding="utf-8")

    after = path.read_bytes()
    decoded = after.decode("utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    if any(forbidden.values()):
        raise SystemExit(f"forbidden token audit failed: {forbidden}")

    print(json.dumps({
        "schema": "qym-probe43-gamma-v2",
        "variant": variant,
        "input_sha256": hashlib.sha256(before).hexdigest(),
        "input_blob": git_blob(before),
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
