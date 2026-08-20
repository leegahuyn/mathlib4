#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

PROOF = r'''theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
  have hentries :
      ((gamma 0 0 : ℤ) : ZMod 2) = 1 ∧
        ((gamma 0 1 : ℤ) : ZMod 2) = 0 ∧
          ((gamma 1 0 : ℤ) : ZMod 2) = 0 ∧
            ((gamma 1 1 : ℤ) : ZMod 2) = 1 :=
    CongruenceSubgroup.Gamma_mem.mp hGamma
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvS
  · exact hcentral
  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      norm_num [ModularGroup.coe_S, ModularGroup.coe_T,
        ModularGroup.coe_T_inv, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two] at hentries
'''

DECL_RE = re.compile(
    r"(?ms)^theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\b.*?"
    r"(?=^/-! ## 2\.)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: qym_probe44b_gamma_conjunction.py QYM.lean")
    path = Path(sys.argv[1])
    before = path.read_bytes()
    text = before.decode("utf-8")
    matches = list(DECL_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected one gamma theorem, found {len(matches)}")
    match = matches[0]
    text = text[:match.start()] + PROOF + "\n" + text[match.end():]
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
        "schema": "qym-probe44b-gamma-conjunction-v1",
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
