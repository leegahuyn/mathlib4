#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

VARIANTS = {
    "entry_norm_num",
    "entry_subst",
    "membership_norm_num",
    "simp_all",
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

SIMPS = """ModularGroup.S, ModularGroup.T, ModularGroup.coe_T_zpow,
        Matrix.mul_apply, Fin.sum_univ_two, SL2_inv_expl"""

PROOFS = {
    "entry_norm_num": HEADER + """  have h01 : ((gamma 0 1 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1
  have h10 : ((gamma 1 0 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1
""" + CLASSIFY + """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      norm_num [""" + SIMPS + """] at h01 h10
""",
    "entry_subst": HEADER + """  have h01 : ((gamma 0 1 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1
  have h10 : ((gamma 1 0 : ℤ) : ZMod 2) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1
""" + CLASSIFY + """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with hMatrix | hMatrix
    · subst gamma
      norm_num [""" + SIMPS + """] at h01 h10
    · subst gamma
      norm_num [""" + SIMPS + """] at h01 h10
""",
    "membership_norm_num": HEADER + CLASSIFY + """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      norm_num [CongruenceSubgroup.Gamma_mem,
        """ + SIMPS + """] at hGamma
""",
    "simp_all": HEADER + CLASSIFY + """  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      simp_all [CongruenceSubgroup.Gamma_mem,
        """ + SIMPS + """]
""",
}

DECL_RE = re.compile(
    r"(?ms)^theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\b.*?"
    r"(?=^/--|^theorem\s|^lemma\s|^noncomputable\s+def\s|^def\s|^section\s|^end\s)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_probe41_gamma2.py VARIANT QYM.lean")
    variant, file_name = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant: {variant}")

    path = Path(file_name)
    before = path.read_bytes()
    text = before.decode("utf-8")
    matches = list(DECL_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected exactly one gammaTwo declaration, found {len(matches)}")
    m = matches[0]
    replacement = "set_option maxHeartbeats 4000000 in\n" + PROOFS[variant] + "\n"
    text = text[:m.start()] + replacement + text[m.end():]
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
        "schema": "qym-probe41-gamma2-v1",
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
