#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASELINE_SHA256 = "313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e"
BASELINE_BLOB = "ff49510790dd7ca136bf34c3ec7150617ee1c241"

OLD = '''theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvS
  · exact hcentral
  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      norm_num [CongruenceSubgroup.Gamma_mem,
        ModularGroup.S, ModularGroup.T] at hGamma
'''

SIMP_SET = '''CongruenceSubgroup.Gamma_mem,
        Matrix.SpecialLinearGroup.SL2_inv_expl,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_fin_two,
        ModularGroup.S, ModularGroup.T'''

ENTRY_HEADER = '''  have h01 : ((gamma 0 1 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1
  have h10 : ((gamma 1 0 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1
'''

COMMON_CASES = '''  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvS
  · exact hcentral
  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
'''

PREFIX = '''theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
'''

VARIANTS = {
    "entry_solve": PREFIX + ENTRY_HEADER + COMMON_CASES + f'''    all_goals
      exfalso
      solve
      | norm_num [{SIMP_SET}] at h01
      | norm_num [{SIMP_SET}] at h10
''',
    "membership_norm": PREFIX + COMMON_CASES + f'''    all_goals
      exfalso
      norm_num [{SIMP_SET}] at hGamma
''',
    "entry_simp_all": PREFIX + ENTRY_HEADER + COMMON_CASES + f'''    all_goals
      exfalso
      simp_all only [{SIMP_SET},
        Int.cast_neg, neg_eq_zero, one_ne_zero]
''',
}


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit(f"usage: {sys.argv[0]} <{'|'.join(VARIANTS)}> QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    path = Path(filename)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASELINE_SHA256:
        raise SystemExit("baseline SHA256 mismatch")
    if git_blob(before) != BASELINE_BLOB:
        raise SystemExit("baseline Git blob mismatch")
    text = before.decode("utf-8")
    count = text.count(OLD)
    if count != 1:
        raise SystemExit(f"C01 theorem replacement count = {count}, expected 1")
    text = text.replace(OLD, VARIANTS[variant], 1)
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
        raise SystemExit(f"forbidden-token audit failed: {forbidden}")
    result = {
        "schema": "qym-c01-variants-v1",
        "variant": variant,
        "input_sha256": BASELINE_SHA256,
        "input_blob": BASELINE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "fixed_producers_targeted": [
            "gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed"
        ],
        "forbidden": forbidden,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
