#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "00f2c8ba7fc0329b04ae67c5a67b5814f8118b14222a7831a0401c9d3d374e53"
INPUT_BLOB = "ee2faeaf281215b0e9b304a96ccdce3e8cdc0ffb"
OUTPUT_SHA256 = "98feaf0246794f69ee43aac1e03b0e19bdef46999682c6a000ee5a9c842b3814"
OUTPUT_BLOB = "ea635b68de7b43d673f7f485362f772d264beb85"
FULL_PATH = Path(".github/qym_fastlane_full.lean")

BASE_HELPERS = r'''lemma qym_tinv00 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 0 = (1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 0 0)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two] at h
  exact h

lemma qym_tinvS_upper_entry :
    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  change
    (∑ k : Fin 2,
      (ModularGroup.T⁻¹).val 0 k * ModularGroup.S.val k 1) = -1
  simp only [Fin.sum_univ_two]
  norm_num [ModularGroup.S, qym_tinv00]

lemma qym_neg_tinvS_upper_entry :
    (-(ModularGroup.T⁻¹ * ModularGroup.S) : SL(2, ℤ)) 0 1 = (1 : ℤ) := by
  simp [qym_tinvS_upper_entry]

theorem qym_tinvS_not_mem_gammaTwo :
    ModularGroup.T⁻¹ * ModularGroup.S ∉
      CongruenceSubgroup.Gamma 2 := by
  intro hmem
  have hUpper := (CongruenceSubgroup.Gamma_mem.mp hmem).2.1
  rw [qym_tinvS_upper_entry] at hUpper
  norm_num at hUpper

theorem qym_neg_tinvS_not_mem_gammaTwo :
    -(ModularGroup.T⁻¹ * ModularGroup.S) ∉
      CongruenceSubgroup.Gamma 2 := by
  intro hmem
  have hUpper := (CongruenceSubgroup.Gamma_mem.mp hmem).2.1
  rw [qym_neg_tinvS_upper_entry] at hUpper
  norm_num at hUpper

'''

OLD_TINV01 = r'''lemma qym_tinv01 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 0 1)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two, qym_tinv00] at h
  exact h
'''

NEW_TINV01 = r'''lemma qym_tinv01 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 0 1)
    (inv_mul_cancel ModularGroup.T)
  change
    (∑ k : Fin 2,
      (ModularGroup.T⁻¹).val 0 k * ModularGroup.T.val k 1) = 0 at h
  simp only [Fin.sum_univ_two] at h
  norm_num [ModularGroup.T] at h
  rw [qym_tinv00] at h
  omega
'''

OLD_TST = r'''lemma qym_TST_lower_entry :
    (ModularGroup.T * ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 0 =
      (1 : ℤ) := by
  change
    (∑ k : Fin 2,
      (ModularGroup.T * ModularGroup.S).val 1 k * ModularGroup.T.val k 0) = 1
  simp only [Fin.sum_univ_two]
  norm_num [qym_TS_lower_entry, qym_TS_11_entry, ModularGroup.T]
'''

NEW_TST = r'''lemma qym_TST_lower_entry :
    (ModularGroup.T * ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 0 =
      (1 : ℤ) := by
  change
    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 *
        ModularGroup.T 0 0 +
      (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 *
        ModularGroup.T 1 0 = 1
  rw [qym_TS_lower_entry, qym_TS_11_entry]
  norm_num [ModularGroup.T]
'''

DOC_ANCHOR = '''/-- A level-two matrix fixing a point of the closed modular fundamental
domain is central.  All exceptional elliptic alternatives in the modular
stabilizer classification have a matrix entry different from the identity
modulo two. -/
'''
THEOREM_MARKER = "theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed"
NEXT_SECTION = "\n\n/-! ## 2. Arbitrary fixed points -/"

FORBIDDEN = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "global_axiom": r"(?m)^\s*axiom\s+",
    "unsafe": r"(?m)^\s*unsafe\s+",
    "native_decide": r"\bnative_decide\b",
    "Lean.ofReduceBool": r"Lean\.ofReduceBool",
    "maxHeartbeats_zero": r"set_option\s+maxHeartbeats\s+0\b",
}


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def counts(text: str) -> dict[str, int]:
    return {name: len(re.findall(pattern, text)) for name, pattern in FORBIDDEN.items()}


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: qym_fastlane_apply.py QYM.lean")
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    assert git_blob(raw) == INPUT_BLOB
    original = raw.decode("utf-8")
    before = counts(original)

    body = FULL_PATH.read_text(encoding="utf-8")
    assert body.count(OLD_TINV01) == 1
    assert body.count(OLD_TST) == 1
    body = body.replace(OLD_TINV01, NEW_TINV01, 1)
    body = body.replace(OLD_TST, NEW_TST, 1)
    theorem_pos = body.index("theorem qym_gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed")
    helper_tail = body[:theorem_pos]
    corrected_theorem = body[theorem_pos:].replace(
        "theorem qym_gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed",
        THEOREM_MARKER,
        1,
    ).rstrip()

    assert original.count(DOC_ANCHOR) == 1
    updated = original.replace(DOC_ANCHOR, BASE_HELPERS + helper_tail + DOC_ANCHOR, 1)
    start = updated.index(THEOREM_MARKER)
    end = updated.index(NEXT_SECTION, start)
    old_theorem = updated[start:end]
    assert old_theorem.count("all_goals") == 2
    updated = updated[:start] + corrected_theorem + updated[end:]

    after = counts(updated)
    assert after == before, (before, after)
    path.write_text(updated, encoding="utf-8")
    result = path.read_bytes()
    sha256 = hashlib.sha256(result).hexdigest()
    blob = git_blob(result)
    assert sha256 == OUTPUT_SHA256, (sha256, OUTPUT_SHA256)
    assert blob == OUTPUT_BLOB, (blob, OUTPUT_BLOB)

    print(json.dumps({
        "schema": "qym-fastlane-probe35-gammatwo-v1",
        "input_sha256": INPUT_SHA256,
        "input_blob": INPUT_BLOB,
        "candidate_sha256": sha256,
        "candidate_blob": blob,
        "bytes": len(result),
        "lf": result.count(b"\n"),
        "forbidden_before": before,
        "forbidden_after": after,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
