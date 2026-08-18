#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "00f2c8ba7fc0329b04ae67c5a67b5814f8118b14222a7831a0401c9d3d374e53"
INPUT_BLOB = "ee2faeaf281215b0e9b304a96ccdce3e8cdc0ffb"
OUTPUT_SHA256 = "55ae6e4e42654ff1140da04785758724c34e473113b621ec267ecf1d791ac75c"
OUTPUT_BLOB = "a23c17e4ee6852b23b2e1e1a5ffe8b4b19e12dff"

OLD_GAMMA = '''theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed
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

NEW_GAMMA = '''private theorem qymGammaTwo_tinv_upper_entry :
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

OLD_HOROCYCLE = '''  simp only [actualFixedPhaseCuspHorocyclePoint,
    actualFixedPhaseHorizontalHorocyclePoint,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  rw [div_eq_mul_inv]
  apply ContDiff.mul
  · fun_prop
  · apply ContDiff.inv
    · fun_prop
    · exact hden
'''
NEW_HOROCYCLE = '''  simp only [actualFixedPhaseCuspHorocyclePoint,
    actualFixedPhaseHorizontalHorocyclePoint,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · exact hden
'''
OLD_NAMED_TRACE = '''  change ContDiff ℝ ∞
    (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘
      fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ))
  exact hcomp
'''
NEW_NAMED_TRACE = '''  simpa [actualFixedPhaseNamedCuspTraceRepresentative,
    Function.comp_def] using hcomp
'''

def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: qym_fastlane_patch.py QYM.lean")
    path = Path(sys.argv[1])
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != INPUT_SHA256:
        raise SystemExit("input SHA256 mismatch")
    if git_blob(before) != INPUT_BLOB:
        raise SystemExit("input Git blob mismatch")

    text = before.decode("utf-8")
    replacements = [
        ("gammaTwo", OLD_GAMMA, NEW_GAMMA),
        ("horocycle", OLD_HOROCYCLE, NEW_HOROCYCLE),
        ("namedTrace", OLD_NAMED_TRACE, NEW_NAMED_TRACE),
    ]
    for label, old, new in replacements:
        count = text.count(old)
        if count != 1:
            raise SystemExit(f"{label} replacement count = {count}, expected 1")
        text = text.replace(old, new, 1)

    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    sha256 = hashlib.sha256(after).hexdigest()
    blob = git_blob(after)
    if sha256 != OUTPUT_SHA256 or blob != OUTPUT_BLOB:
        raise SystemExit(f"unexpected output: {sha256} {blob}")

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

    print(json.dumps({
        "schema": "qym-fastlane-probe35-batch1-v1",
        "input_sha256": INPUT_SHA256,
        "input_blob": INPUT_BLOB,
        "candidate_sha256": sha256,
        "candidate_blob": blob,
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "fixed_producers": [
            "gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed",
            "actualFixedPhaseCuspHorocyclePoint_coe_contDiff",
            "actualFixedPhaseNamedCuspTraceRepresentative_contDiff",
        ],
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
