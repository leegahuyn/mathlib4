#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "00f2c8ba7fc0329b04ae67c5a67b5814f8118b14222a7831a0401c9d3d374e53"
START = "theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\n"
END = "\n/-! ## 2. Arbitrary fixed points -/"

REPLACEMENT = r'''private theorem qymGammaTwo_tinv_upper_entry :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  rw [← zpow_neg_one, ModularGroup.coe_T_zpow]
  norm_num

private theorem qymGammaTwo_tinv00 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 0 = (1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 0 0)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two] at h
  exact h

private theorem qymGammaTwo_tinv10 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 1 0 = (0 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 1 0)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two] at h
  exact h

private theorem qymGammaTwo_tinv11 :
    (ModularGroup.T⁻¹ : SL(2, ℤ)) 1 1 = (1 : ℤ) := by
  have h := congrArg (fun g : SL(2, ℤ) => g 1 1)
    (inv_mul_cancel ModularGroup.T)
  norm_num [Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_fin_two,
    qymGammaTwo_tinv10] at h
  exact h

private theorem qymGammaTwo_t_upper_entry :
    (ModularGroup.T : SL(2, ℤ)) 0 1 = (1 : ℤ) := by
  norm_num [ModularGroup.T]

private theorem qymGammaTwo_s_upper_entry :
    (ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  norm_num [ModularGroup.S]

private theorem qymGammaTwo_ts_upper_entry :
    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  change
    ModularGroup.T.val 0 0 * ModularGroup.S.val 0 1 +
      ModularGroup.T.val 0 1 * ModularGroup.S.val 1 1 = -1
  norm_num [ModularGroup.T, ModularGroup.S]

private theorem qymGammaTwo_tinvS_lower_entry :
    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 1 0 = (1 : ℤ) := by
  change
    (ModularGroup.T⁻¹).val 1 0 * ModularGroup.S.val 0 0 +
      (ModularGroup.T⁻¹).val 1 1 * ModularGroup.S.val 1 0 = 1
  norm_num [ModularGroup.S, qymGammaTwo_tinv10,
    qymGammaTwo_tinv11]

private theorem qymGammaTwo_tinvS_11_entry :
    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 1 1 = (0 : ℤ) := by
  change
    (ModularGroup.T⁻¹).val 1 0 * ModularGroup.S.val 0 1 +
      (ModularGroup.T⁻¹).val 1 1 * ModularGroup.S.val 1 1 = 0
  norm_num [ModularGroup.S, qymGammaTwo_tinv10,
    qymGammaTwo_tinv11]

private theorem qymGammaTwo_tinvSTinv_lower_entry :
    (ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ :
      SL(2, ℤ)) 1 0 = (1 : ℤ) := by
  change
    (ModularGroup.T⁻¹ * ModularGroup.S).val 1 0 *
        (ModularGroup.T⁻¹).val 0 0 +
      (ModularGroup.T⁻¹ * ModularGroup.S).val 1 1 *
        (ModularGroup.T⁻¹).val 1 0 = 1
  norm_num [qymGammaTwo_tinvS_lower_entry,
    qymGammaTwo_tinvS_11_entry, qymGammaTwo_tinv00,
    qymGammaTwo_tinv10]

private theorem qymGammaTwo_stinv_upper_entry :
    (ModularGroup.S * ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  change
    ModularGroup.S.val 0 0 * (ModularGroup.T⁻¹).val 0 1 +
      ModularGroup.S.val 0 1 * (ModularGroup.T⁻¹).val 1 1 = -1
  norm_num [ModularGroup.S, qymGammaTwo_tinv_upper_entry,
    qymGammaTwo_tinv11]

private theorem qymGammaTwo_st_upper_entry :
    (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  change
    ModularGroup.S.val 0 0 * ModularGroup.T.val 0 1 +
      ModularGroup.S.val 0 1 * ModularGroup.T.val 1 1 = -1
  norm_num [ModularGroup.S, ModularGroup.T]

private theorem qymGammaTwo_ts_lower_entry :
    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = (1 : ℤ) := by
  change
    ModularGroup.T.val 1 0 * ModularGroup.S.val 0 0 +
      ModularGroup.T.val 1 1 * ModularGroup.S.val 1 0 = 1
  norm_num [ModularGroup.T, ModularGroup.S]

private theorem qymGammaTwo_ts_11_entry :
    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = (0 : ℤ) := by
  change
    ModularGroup.T.val 1 0 * ModularGroup.S.val 0 1 +
      ModularGroup.T.val 1 1 * ModularGroup.S.val 1 1 = 0
  norm_num [ModularGroup.T, ModularGroup.S]

private theorem qymGammaTwo_tst_lower_entry :
    (ModularGroup.T * ModularGroup.S * ModularGroup.T :
      SL(2, ℤ)) 1 0 = (1 : ℤ) := by
  change
    (ModularGroup.T * ModularGroup.S).val 1 0 *
        ModularGroup.T.val 0 0 +
      (ModularGroup.T * ModularGroup.S).val 1 1 *
        ModularGroup.T.val 1 0 = 1
  rw [qymGammaTwo_ts_lower_entry, qymGammaTwo_ts_11_entry]
  norm_num [ModularGroup.T]

private theorem qymGammaTwo_tinvS_upper_entry :
    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
  change
    (ModularGroup.T⁻¹).val 0 0 * ModularGroup.S.val 0 1 +
      (ModularGroup.T⁻¹).val 0 1 * ModularGroup.S.val 1 1 = -1
  norm_num [ModularGroup.S, qymGammaTwo_tinv00,
    qymGammaTwo_tinv_upper_entry]

/-- A level-two matrix fixing a point of the closed modular fundamental
 domain is central.  All exceptional elliptic alternatives in the modular
 stabilizer classification have a matrix entry different from the identity
 modulo two. -/
theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
  have hUpper : (((gamma 0 1 : ℤ) : ZMod 2)) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1
  have hLower : (((gamma 1 0 : ℤ) : ZMod 2)) = 0 :=
    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1
  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvS
  · exact hcentral
  · rcases hT.1 with rfl | rfl <;> exfalso <;>
      norm_num [qymGammaTwo_t_upper_entry] at hUpper
  · rcases hTinv.1 with rfl | rfl <;> exfalso <;>
      norm_num [qymGammaTwo_tinv_upper_entry] at hUpper
  · rcases hS.1 with rfl | rfl <;> exfalso <;>
      norm_num [qymGammaTwo_s_upper_entry] at hUpper
  · rcases hTS.1 with rfl | rfl <;> exfalso <;>
      norm_num [qymGammaTwo_ts_upper_entry] at hUpper
  · rcases hTinvSTinv.1 with rfl | rfl <;> exfalso <;>
      norm_num [qymGammaTwo_tinvSTinv_lower_entry] at hLower
  · rcases hSTinv.1 with rfl | rfl <;> exfalso <;>
      norm_num [qymGammaTwo_stinv_upper_entry] at hUpper
  · rcases hST.1 with rfl | rfl <;> exfalso <;>
      norm_num [qymGammaTwo_st_upper_entry] at hUpper
  · rcases hTST.1 with rfl | rfl <;> exfalso <;>
      norm_num [qymGammaTwo_tst_lower_entry] at hLower
  · rcases hTinvS.1 with rfl | rfl <;> exfalso <;>
      norm_num [qymGammaTwo_tinvS_upper_entry] at hUpper
'''


def git_blob_sha(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def main() -> None:
    if len(sys.argv) not in (2, 3):
        raise SystemExit("usage: qym_probe40_full_stabilizer_patch.py QYM.lean [result.json]")
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != INPUT_SHA256:
        raise SystemExit(f"input SHA mismatch: expected {INPUT_SHA256}, got {actual}")
    text = raw.decode("utf-8")
    if text.count(START) != 1:
        raise SystemExit(f"expected one theorem start, found {text.count(START)}")
    start = text.index(START)
    if END not in text[start:]:
        raise SystemExit("end marker not found")
    end = text.index(END, start)
    old = text[start:end]
    if "all_goals" not in old or "cases_of_mem_fd_smul_mem_fd" not in old:
        raise SystemExit("unexpected original theorem body")
    for name in (
        "qymGammaTwo_tinv_upper_entry",
        "qymGammaTwo_tinv00",
        "qymGammaTwo_tst_lower_entry",
    ):
        if name in text:
            raise SystemExit(f"helper name already exists: {name}")
    text = text[:start] + REPLACEMENT.rstrip() + "\n" + text[end:]
    path.write_text(text, encoding="utf-8", newline="\n")
    result_raw = path.read_bytes()
    decoded = result_raw.decode("utf-8")
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
    result = {
        "schema": "qym-probe40-full-stabilizer-patch-v2",
        "input_sha256": actual,
        "candidate_qym_sha256": hashlib.sha256(result_raw).hexdigest(),
        "candidate_qym_blob": git_blob_sha(result_raw),
        "bytes": len(result_raw),
        "lf": result_raw.count(b"\n"),
        "replaced_bytes": len(old.encode("utf-8")),
        "forbidden": forbidden,
    }
    if len(sys.argv) == 3:
        Path(sys.argv[2]).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
