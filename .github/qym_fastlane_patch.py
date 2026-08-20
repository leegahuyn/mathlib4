#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "00f2c8ba7fc0329b04ae67c5a67b5814f8118b14222a7831a0401c9d3d374e53"
INPUT_BLOB = "ee2faeaf281215b0e9b304a96ccdce3e8cdc0ffb"
OUTPUT_SHA256 = "a9ff4b519780a69e3fa9d7e68ddc65a69e9ec43f76f2f0383360c038c13f7845"
OUTPUT_BLOB = "43b3dc4f72fcc6fc9399e9c0bd768c297dcfabb6"

GAMMA_PROOF = r"""theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
    {gamma : SL(2, ℤ)} {z : ℍ}
    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)
    (hz : z ∈ ModularGroup.fd)
    (hfix : gamma • z = z) :
    gamma = 1 ∨ gamma = -1 := by
  have hInv00 : (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 0 = (1 : ℤ) := by
    have h := congrArg (fun g : SL(2, ℤ) => g 0 0)
      (inv_mul_cancel ModularGroup.T)
    norm_num [Matrix.SpecialLinearGroup.coe_mul,
      ModularGroup.T, Matrix.mul_fin_two] at h
    exact h
  have hInv10 : (ModularGroup.T⁻¹ : SL(2, ℤ)) 1 0 = (0 : ℤ) := by
    have h := congrArg (fun g : SL(2, ℤ) => g 1 0)
      (inv_mul_cancel ModularGroup.T)
    norm_num [Matrix.SpecialLinearGroup.coe_mul,
      ModularGroup.T, Matrix.mul_fin_two] at h
    exact h
  have hInv11 : (ModularGroup.T⁻¹ : SL(2, ℤ)) 1 1 = (1 : ℤ) := by
    have h := congrArg (fun g : SL(2, ℤ) => g 1 1)
      (inv_mul_cancel ModularGroup.T)
    norm_num [Matrix.SpecialLinearGroup.coe_mul,
      ModularGroup.T, Matrix.mul_fin_two, hInv10] at h
    exact h
  have hInv01 : (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
    rw [← zpow_neg_one, ModularGroup.coe_T_zpow]
    norm_num

  have hTSUpper :
      (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
    change
      ModularGroup.T.val 0 0 * ModularGroup.S.val 0 1 +
        ModularGroup.T.val 0 1 * ModularGroup.S.val 1 1 = -1
    norm_num [ModularGroup.T, ModularGroup.S]
  have hTinvSLower :
      (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 1 0 = (1 : ℤ) := by
    change
      (ModularGroup.T⁻¹).val 1 0 * ModularGroup.S.val 0 0 +
        (ModularGroup.T⁻¹).val 1 1 * ModularGroup.S.val 1 0 = 1
    norm_num [ModularGroup.S, hInv10, hInv11]
  have hTinvS11 :
      (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 1 1 = (0 : ℤ) := by
    change
      (ModularGroup.T⁻¹).val 1 0 * ModularGroup.S.val 0 1 +
        (ModularGroup.T⁻¹).val 1 1 * ModularGroup.S.val 1 1 = 0
    norm_num [ModularGroup.S, hInv10, hInv11]
  have hTinvSTinvLower :
      (ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ : SL(2, ℤ)) 1 0 =
        (1 : ℤ) := by
    change
      (ModularGroup.T⁻¹ * ModularGroup.S).val 1 0 *
          (ModularGroup.T⁻¹).val 0 0 +
        (ModularGroup.T⁻¹ * ModularGroup.S).val 1 1 *
          (ModularGroup.T⁻¹).val 1 0 = 1
    rw [hTinvSLower, hTinvS11, hInv00, hInv10]
    norm_num
  have hSTinvUpper :
      (ModularGroup.S * ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
    change
      ModularGroup.S.val 0 0 * (ModularGroup.T⁻¹).val 0 1 +
        ModularGroup.S.val 0 1 * (ModularGroup.T⁻¹).val 1 1 = -1
    norm_num [ModularGroup.S, hInv01, hInv11]
  have hSTUpper :
      (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
    change
      ModularGroup.S.val 0 0 * ModularGroup.T.val 0 1 +
        ModularGroup.S.val 0 1 * ModularGroup.T.val 1 1 = -1
    norm_num [ModularGroup.S, ModularGroup.T]
  have hTSLower :
      (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = (1 : ℤ) := by
    change
      ModularGroup.T.val 1 0 * ModularGroup.S.val 0 0 +
        ModularGroup.T.val 1 1 * ModularGroup.S.val 1 0 = 1
    norm_num [ModularGroup.T, ModularGroup.S]
  have hTS11 :
      (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = (0 : ℤ) := by
    change
      ModularGroup.T.val 1 0 * ModularGroup.S.val 0 1 +
        ModularGroup.T.val 1 1 * ModularGroup.S.val 1 1 = 0
    norm_num [ModularGroup.T, ModularGroup.S]
  have hTSTLower :
      (ModularGroup.T * ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 1 0 =
        (1 : ℤ) := by
    change
      (ModularGroup.T * ModularGroup.S).val 1 0 * ModularGroup.T.val 0 0 +
        (ModularGroup.T * ModularGroup.S).val 1 1 * ModularGroup.T.val 1 0 = 1
    rw [hTSLower, hTS11]
    norm_num [ModularGroup.T]
  have hTinvSUpper :
      (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
    change
      (ModularGroup.T⁻¹).val 0 0 * ModularGroup.S.val 0 1 +
        (ModularGroup.T⁻¹).val 0 1 * ModularGroup.S.val 1 1 = -1
    norm_num [ModularGroup.S, hInv00]

  have pairNotMemUpperOne {g : SL(2, ℤ)} (h : g 0 1 = (1 : ℤ)) :
      g ∉ CongruenceSubgroup.Gamma 2 ∧
        -g ∉ CongruenceSubgroup.Gamma 2 := by
    constructor
    · intro hg
      have hu := (CongruenceSubgroup.Gamma_mem.mp hg).2.1
      rw [h] at hu
      norm_num at hu
    · intro hg
      have hu := (CongruenceSubgroup.Gamma_mem.mp hg).2.1
      have hn : (-g : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by
        change -(g 0 1) = -1
        rw [h]
      rw [hn] at hu
      norm_num at hu
  have pairNotMemUpperNegOne {g : SL(2, ℤ)} (h : g 0 1 = (-1 : ℤ)) :
      g ∉ CongruenceSubgroup.Gamma 2 ∧
        -g ∉ CongruenceSubgroup.Gamma 2 := by
    constructor
    · intro hg
      have hu := (CongruenceSubgroup.Gamma_mem.mp hg).2.1
      rw [h] at hu
      norm_num at hu
    · intro hg
      have hu := (CongruenceSubgroup.Gamma_mem.mp hg).2.1
      have hn : (-g : SL(2, ℤ)) 0 1 = (1 : ℤ) := by
        change -(g 0 1) = 1
        rw [h]
        norm_num
      rw [hn] at hu
      norm_num at hu
  have pairNotMemLowerOne {g : SL(2, ℤ)} (h : g 1 0 = (1 : ℤ)) :
      g ∉ CongruenceSubgroup.Gamma 2 ∧
        -g ∉ CongruenceSubgroup.Gamma 2 := by
    constructor
    · intro hg
      have hl := (CongruenceSubgroup.Gamma_mem.mp hg).2.2.1
      rw [h] at hl
      norm_num at hl
    · intro hg
      have hl := (CongruenceSubgroup.Gamma_mem.mp hg).2.2.1
      have hn : (-g : SL(2, ℤ)) 1 0 = (-1 : ℤ) := by
        change -(g 1 0) = -1
        rw [h]
      rw [hn] at hl
      norm_num at hl

  have hTNo := pairNotMemUpperOne
    (g := ModularGroup.T) (by norm_num [ModularGroup.T])
  have hTinvNo := pairNotMemUpperNegOne
    (g := ModularGroup.T⁻¹) hInv01
  have hSNo := pairNotMemUpperNegOne
    (g := ModularGroup.S) (by norm_num [ModularGroup.S])
  have hTSNo := pairNotMemUpperNegOne
    (g := ModularGroup.T * ModularGroup.S) hTSUpper
  have hTinvSTinvNo := pairNotMemLowerOne
    (g := ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹)
    hTinvSTinvLower
  have hSTinvNo := pairNotMemUpperNegOne
    (g := ModularGroup.S * ModularGroup.T⁻¹) hSTinvUpper
  have hSTNo := pairNotMemUpperNegOne
    (g := ModularGroup.S * ModularGroup.T) hSTUpper
  have hTSTNo := pairNotMemLowerOne
    (g := ModularGroup.T * ModularGroup.S * ModularGroup.T) hTSTLower
  have hTinvSNo := pairNotMemUpperNegOne
    (g := ModularGroup.T⁻¹ * ModularGroup.S) hTinvSUpper

  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with
    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |
      hSTinv | hST | hTST | hTinvS
  · exact hcentral
  · rcases hT.1 with rfl | rfl
    · exact (hTNo.1 hGamma).elim
    · exact (hTNo.2 hGamma).elim
  · rcases hTinv.1 with rfl | rfl
    · exact (hTinvNo.1 hGamma).elim
    · exact (hTinvNo.2 hGamma).elim
  · rcases hS.1 with rfl | rfl
    · exact (hSNo.1 hGamma).elim
    · exact (hSNo.2 hGamma).elim
  · rcases hTS.1 with rfl | rfl
    · exact (hTSNo.1 hGamma).elim
    · exact (hTSNo.2 hGamma).elim
  · rcases hTinvSTinv.1 with rfl | rfl
    · exact (hTinvSTinvNo.1 hGamma).elim
    · exact (hTinvSTinvNo.2 hGamma).elim
  · rcases hSTinv.1 with rfl | rfl
    · exact (hSTinvNo.1 hGamma).elim
    · exact (hSTinvNo.2 hGamma).elim
  · rcases hST.1 with rfl | rfl
    · exact (hSTNo.1 hGamma).elim
    · exact (hSTNo.2 hGamma).elim
  · rcases hTST.1 with rfl | rfl
    · exact (hTSTNo.1 hGamma).elim
    · exact (hTSTNo.2 hGamma).elim
  · rcases hTinvS.1 with rfl | rfl
    · exact (hTinvSNo.1 hGamma).elim
    · exact (hTinvSNo.2 hGamma).elim"""


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: qym_fastlane_patch.py QYM.lean")
    path = Path(sys.argv[1])
    before = path.read_bytes()
    assert hashlib.sha256(before).hexdigest() == INPUT_SHA256
    assert git_blob(before) == INPUT_BLOB
    text = before.decode("utf-8")

    gamma_start = text.index("theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed")
    gamma_end = text.index("\n\n/-! ## 2. Arbitrary fixed points -/", gamma_start)
    text = text[:gamma_start] + GAMMA_PROOF + text[gamma_end:]

    tail_start = text.index("theorem coordinateHamiltonianForm_re_self")
    tail_end = text.index("\n\n/-- The displayed positive shift", tail_start)
    tail = text[tail_start:tail_end]
    assert tail.endswith("  simp")
    text = text[:tail_start] + tail[:-len("  simp")] + "  norm_num" + text[tail_end:]

    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }
    assert not any(forbidden.values()), forbidden

    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    sha = hashlib.sha256(after).hexdigest()
    blob = git_blob(after)
    assert sha == OUTPUT_SHA256, (sha, OUTPUT_SHA256)
    assert blob == OUTPUT_BLOB, (blob, OUTPUT_BLOB)
    print(json.dumps({
        "schema": "qym-fastlane-gamma-tail-v1",
        "input_sha256": INPUT_SHA256,
        "input_blob": INPUT_BLOB,
        "candidate_sha256": sha,
        "candidate_blob": blob,
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "repairs": [
            "gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed",
            "coordinateHamiltonianForm_re_self",
        ],
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
