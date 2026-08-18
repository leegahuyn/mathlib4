#!/usr/bin/env python3
from __future__ import annotations

# Trigger a second push after workflow registration; proof output is unchanged.
from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "00f2c8ba7fc0329b04ae67c5a67b5814f8118b14222a7831a0401c9d3d374e53"
INPUT_BLOB = "ee2faeaf281215b0e9b304a96ccdce3e8cdc0ffb"
OUTPUT_SHA256 = "55ae6e4e42654ff1140da04785758724c34e473113b621ec267ecf1d791ac75c"
OUTPUT_BLOB = "a23c17e4ee6852b23b2e1e1a5ffe8b4b19e12dff"

OLD_GAMMA = 'theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\n    {gamma : SL(2, ℤ)} {z : ℍ}\n    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)\n    (hz : z ∈ ModularGroup.fd)\n    (hfix : gamma • z = z) :\n    gamma = 1 ∨ gamma = -1 := by\n  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with\n    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |\n      hSTinv | hST | hTST | hTinvS\n  · exact hcentral\n  all_goals\n    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩\n    rcases hMatrix with rfl | rfl\n    all_goals\n      norm_num [CongruenceSubgroup.Gamma_mem,\n        ModularGroup.S, ModularGroup.T] at hGamma\n'
NEW_GAMMA = 'private theorem qymGammaTwo_tinv_upper_entry :\n    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by\n  rw [← zpow_neg_one, ModularGroup.coe_T_zpow]\n  norm_num\n\nprivate theorem qymGammaTwo_tinv00 :\n    (ModularGroup.T⁻¹ : SL(2, ℤ)) 0 0 = (1 : ℤ) := by\n  have h := congrArg (fun g : SL(2, ℤ) => g 0 0)\n    (inv_mul_cancel ModularGroup.T)\n  norm_num [Matrix.SpecialLinearGroup.coe_mul,\n    ModularGroup.T, Matrix.mul_fin_two] at h\n  exact h\n\nprivate theorem qymGammaTwo_tinv10 :\n    (ModularGroup.T⁻¹ : SL(2, ℤ)) 1 0 = (0 : ℤ) := by\n  have h := congrArg (fun g : SL(2, ℤ) => g 1 0)\n    (inv_mul_cancel ModularGroup.T)\n  norm_num [Matrix.SpecialLinearGroup.coe_mul,\n    ModularGroup.T, Matrix.mul_fin_two] at h\n  exact h\n\nprivate theorem qymGammaTwo_tinv11 :\n    (ModularGroup.T⁻¹ : SL(2, ℤ)) 1 1 = (1 : ℤ) := by\n  have h := congrArg (fun g : SL(2, ℤ) => g 1 1)\n    (inv_mul_cancel ModularGroup.T)\n  norm_num [Matrix.SpecialLinearGroup.coe_mul,\n    ModularGroup.T, Matrix.mul_fin_two,\n    qymGammaTwo_tinv10] at h\n  exact h\n\nprivate theorem qymGammaTwo_t_upper_entry :\n    (ModularGroup.T : SL(2, ℤ)) 0 1 = (1 : ℤ) := by\n  norm_num [ModularGroup.T]\n\nprivate theorem qymGammaTwo_s_upper_entry :\n    (ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by\n  norm_num [ModularGroup.S]\n\nprivate theorem qymGammaTwo_ts_upper_entry :\n    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by\n  change\n    ModularGroup.T.val 0 0 * ModularGroup.S.val 0 1 +\n      ModularGroup.T.val 0 1 * ModularGroup.S.val 1 1 = -1\n  norm_num [ModularGroup.T, ModularGroup.S]\n\nprivate theorem qymGammaTwo_tinvS_lower_entry :\n    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 1 0 = (1 : ℤ) := by\n  change\n    (ModularGroup.T⁻¹).val 1 0 * ModularGroup.S.val 0 0 +\n      (ModularGroup.T⁻¹).val 1 1 * ModularGroup.S.val 1 0 = 1\n  norm_num [ModularGroup.S, qymGammaTwo_tinv10,\n    qymGammaTwo_tinv11]\n\nprivate theorem qymGammaTwo_tinvS_11_entry :\n    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 1 1 = (0 : ℤ) := by\n  change\n    (ModularGroup.T⁻¹).val 1 0 * ModularGroup.S.val 0 1 +\n      (ModularGroup.T⁻¹).val 1 1 * ModularGroup.S.val 1 1 = 0\n  norm_num [ModularGroup.S, qymGammaTwo_tinv10,\n    qymGammaTwo_tinv11]\n\nprivate theorem qymGammaTwo_tinvSTinv_lower_entry :\n    (ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ :\n      SL(2, ℤ)) 1 0 = (1 : ℤ) := by\n  change\n    (ModularGroup.T⁻¹ * ModularGroup.S).val 1 0 *\n        (ModularGroup.T⁻¹).val 0 0 +\n      (ModularGroup.T⁻¹ * ModularGroup.S).val 1 1 *\n        (ModularGroup.T⁻¹).val 1 0 = 1\n  norm_num [qymGammaTwo_tinvS_lower_entry,\n    qymGammaTwo_tinvS_11_entry, qymGammaTwo_tinv00,\n    qymGammaTwo_tinv10]\n\nprivate theorem qymGammaTwo_stinv_upper_entry :\n    (ModularGroup.S * ModularGroup.T⁻¹ : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by\n  change\n    ModularGroup.S.val 0 0 * (ModularGroup.T⁻¹).val 0 1 +\n      ModularGroup.S.val 0 1 * (ModularGroup.T⁻¹).val 1 1 = -1\n  norm_num [ModularGroup.S, qymGammaTwo_tinv_upper_entry,\n    qymGammaTwo_tinv11]\n\nprivate theorem qymGammaTwo_st_upper_entry :\n    (ModularGroup.S * ModularGroup.T : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by\n  change\n    ModularGroup.S.val 0 0 * ModularGroup.T.val 0 1 +\n      ModularGroup.S.val 0 1 * ModularGroup.T.val 1 1 = -1\n  norm_num [ModularGroup.S, ModularGroup.T]\n\nprivate theorem qymGammaTwo_ts_lower_entry :\n    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = (1 : ℤ) := by\n  change\n    ModularGroup.T.val 1 0 * ModularGroup.S.val 0 0 +\n      ModularGroup.T.val 1 1 * ModularGroup.S.val 1 0 = 1\n  norm_num [ModularGroup.T, ModularGroup.S]\n\nprivate theorem qymGammaTwo_ts_11_entry :\n    (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = (0 : ℤ) := by\n  change\n    ModularGroup.T.val 1 0 * ModularGroup.S.val 0 1 +\n      ModularGroup.T.val 1 1 * ModularGroup.S.val 1 1 = 0\n  norm_num [ModularGroup.T, ModularGroup.S]\n\nprivate theorem qymGammaTwo_tst_lower_entry :\n    (ModularGroup.T * ModularGroup.S * ModularGroup.T :\n      SL(2, ℤ)) 1 0 = (1 : ℤ) := by\n  change\n    (ModularGroup.T * ModularGroup.S).val 1 0 *\n        ModularGroup.T.val 0 0 +\n      (ModularGroup.T * ModularGroup.S).val 1 1 *\n        ModularGroup.T.val 1 0 = 1\n  rw [qymGammaTwo_ts_lower_entry, qymGammaTwo_ts_11_entry]\n  norm_num [ModularGroup.T]\n\nprivate theorem qymGammaTwo_tinvS_upper_entry :\n    (ModularGroup.T⁻¹ * ModularGroup.S : SL(2, ℤ)) 0 1 = (-1 : ℤ) := by\n  change\n    (ModularGroup.T⁻¹).val 0 0 * ModularGroup.S.val 0 1 +\n      (ModularGroup.T⁻¹).val 0 1 * ModularGroup.S.val 1 1 = -1\n  norm_num [ModularGroup.S, qymGammaTwo_tinv00,\n    qymGammaTwo_tinv_upper_entry]\n\ntheorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\n    {gamma : SL(2, ℤ)} {z : ℍ}\n    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)\n    (hz : z ∈ ModularGroup.fd)\n    (hfix : gamma • z = z) :\n    gamma = 1 ∨ gamma = -1 := by\n  have hUpper : (((gamma 0 1 : ℤ) : ZMod 2)) = 0 :=\n    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1\n  have hLower : (((gamma 1 0 : ℤ) : ZMod 2)) = 0 :=\n    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1\n  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with\n    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |\n      hSTinv | hST | hTST | hTinvS\n  · exact hcentral\n  · rcases hT.1 with rfl | rfl <;> exfalso <;>\n      norm_num [qymGammaTwo_t_upper_entry] at hUpper\n  · rcases hTinv.1 with rfl | rfl <;> exfalso <;>\n      norm_num [qymGammaTwo_tinv_upper_entry] at hUpper\n  · rcases hS.1 with rfl | rfl <;> exfalso <;>\n      norm_num [qymGammaTwo_s_upper_entry] at hUpper\n  · rcases hTS.1 with rfl | rfl <;> exfalso <;>\n      norm_num [qymGammaTwo_ts_upper_entry] at hUpper\n  · rcases hTinvSTinv.1 with rfl | rfl <;> exfalso <;>\n      norm_num [qymGammaTwo_tinvSTinv_lower_entry] at hLower\n  · rcases hSTinv.1 with rfl | rfl <;> exfalso <;>\n      norm_num [qymGammaTwo_stinv_upper_entry] at hUpper\n  · rcases hST.1 with rfl | rfl <;> exfalso <;>\n      norm_num [qymGammaTwo_st_upper_entry] at hUpper\n  · rcases hTST.1 with rfl | rfl <;> exfalso <;>\n      norm_num [qymGammaTwo_tst_lower_entry] at hLower\n  · rcases hTinvS.1 with rfl | rfl <;> exfalso <;>\n      norm_num [qymGammaTwo_tinvS_upper_entry] at hUpper\n'
OLD_HOROCYCLE = '  simp only [actualFixedPhaseCuspHorocyclePoint,\n    actualFixedPhaseHorizontalHorocyclePoint,\n    UpperHalfPlane.coe_specialLinearGroup_apply]\n  rw [div_eq_mul_inv]\n  apply ContDiff.mul\n  · fun_prop\n  · apply ContDiff.inv\n    · fun_prop\n    · exact hden\n'
NEW_HOROCYCLE = '  simp only [actualFixedPhaseCuspHorocyclePoint,\n    actualFixedPhaseHorizontalHorocyclePoint,\n    UpperHalfPlane.coe_specialLinearGroup_apply]\n  apply ContDiff.div\n  · fun_prop\n  · fun_prop\n  · exact hden\n'
OLD_NAMED_TRACE = '  change ContDiff ℝ ∞\n    (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘\n      fun x : ℝ =>\n        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ))\n  exact hcomp\n'
NEW_NAMED_TRACE = '  simpa [actualFixedPhaseNamedCuspTraceRepresentative,\n    Function.comp_def] using hcomp\n'

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
