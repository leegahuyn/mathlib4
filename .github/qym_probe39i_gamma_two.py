#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e"
INPUT_BLOB = "ff49510790dd7ca136bf34c3ec7150617ee1c241"
OUTPUT_SHA256 = "d51a4010bcc2d43b5588dfa36504bf50b46d20138dcdbac177b4bfc90d8dee04"
OUTPUT_BLOB = "7e4ea259584e87c935a06f2bb4ad05c717e36c0c"
OUTPUT_BYTES = 2945967
OUTPUT_LF = 62280

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

NEW = '''theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
  have hUpper : (((gamma 0 1 : ℤ) : ZMod 2)) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1
  have hLower : (((gamma 1 0 : ℤ) : ZMod 2)) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1
  have hInv00 :
      (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 0 = (1 : ℤ) := by
    have h := congrArg (fun g : SL(2, ℤ) => g 0 0)
      (inv_mul_cancel ModularGroup.T)
    norm_num [Matrix.SpecialLinearGroup.coe_mul,
      ModularGroup.T, Matrix.mul_fin_two] at h
    exact h
  have hTinvSUpper :
      (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
    change
      (ModularGroup.T⁻¹).val 0 0 * ModularGroup.S.val 0 1 +
        (ModularGroup.T⁻¹).val 0 1 * ModularGroup.S.val 1 1 = -1
    norm_num [ModularGroup.S, hInv00]
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvS
  · exact hcentral
  all_goals
    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩
    rcases hMatrix with rfl | rfl
    all_goals
      exfalso
      all_goals try
        norm_num [ModularGroup.S, ModularGroup.T, ← zpow_neg_one,
          ModularGroup.coe_T_zpow, Matrix.mul_fin_two,
          hTinvSUpper] at hUpper
      all_goals try
        norm_num [ModularGroup.S, ModularGroup.T, ← zpow_neg_one,
          ModularGroup.coe_T_zpow, Matrix.mul_fin_two,
          hTinvSUpper] at hLower
'''


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: qym_probe39i_gamma_two.py QYM.lean")
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    assert git_blob(raw) == INPUT_BLOB
    text = raw.decode("utf-8")
    assert text.count(OLD) == 1, text.count(OLD)
    text = text.replace(OLD, NEW, 1)
    path.write_text(text, encoding="utf-8")
    result = path.read_bytes()
    sha256 = hashlib.sha256(result).hexdigest()
    blob = git_blob(result)
    assert sha256 == OUTPUT_SHA256, (sha256, OUTPUT_SHA256)
    assert blob == OUTPUT_BLOB, (blob, OUTPUT_BLOB)
    assert len(result) == OUTPUT_BYTES, (len(result), OUTPUT_BYTES)
    assert result.count(b"\n") == OUTPUT_LF, (result.count(b"\n"), OUTPUT_LF)
    decoded = result.decode("utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    assert not any(forbidden.values()), forbidden
    print(json.dumps({
        "schema": "qym-probe39i-gamma-two-v1",
        "input_sha256": INPUT_SHA256,
        "input_blob": INPUT_BLOB,
        "candidate_sha256": sha256,
        "candidate_blob": blob,
        "bytes": len(result),
        "lf": result.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
