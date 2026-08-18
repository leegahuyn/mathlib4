#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e"
INPUT_BLOB = "ff49510790dd7ca136bf34c3ec7150617ee1c241"
EXPECTED = {
    "entries": {
        "sha256": "f92f82e87bca5e0433c3778ef53258fd282966229e5f0ad6b9afe13000e4857f",
        "blob": "39de4cd563435c78e2d8a73e6635e00f07f6bba8",
        "bytes": 2945907,
        "lf": 62279
    },
    "gamma": {
        "sha256": "7badd72b1b949b5250c2dbfd761960f1595fcd5348f6e71b05d073eba2c32bdc",
        "blob": "6dcc6c58b972b7e81489403ca08fbeef8f582879",
        "bytes": 2945881,
        "lf": 62279
    },
    "offdiag": {
        "sha256": "a43572af32da48a21bbc2da6ab564fa928d5f3de5890a3156884417c5bb3e161",
        "blob": "86d0f3542066396c08c846d8dce6a346a2ecf969",
        "bytes": 2946070,
        "lf": 62284
    }
}

OLD = 'theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\n    {gamma : SL(2, ℤ)} {z : ℍ}\n    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)\n    (hz : z ∈ ModularGroup.fd)\n    (hfix : gamma • z = z) :\n    gamma = 1 ∨ gamma = -1 := by\n  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with\n    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |\n      hSTinv | hST | hTST | hTinvS\n  · exact hcentral\n  all_goals\n    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩\n    rcases hMatrix with rfl | rfl\n    all_goals\n      norm_num [CongruenceSubgroup.Gamma_mem,\n        ModularGroup.S, ModularGroup.T] at hGamma\n'

VARIANTS = {
    "entries": 'theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\n    {gamma : SL(2, ℤ)} {z : ℍ}\n    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)\n    (hz : z ∈ ModularGroup.fd)\n    (hfix : gamma • z = z) :\n    gamma = 1 ∨ gamma = -1 := by\n  have hTinvMatrix :\n      ModularGroup.T⁻¹ =\n        ⟨!![1, -1; 0, 1], by simp⟩ := by decide\n  have hTSMatrix :\n      ModularGroup.T * ModularGroup.S =\n        ⟨!![1, -1; 1, 0], by simp⟩ := by decide\n  have hTinvSTinvMatrix :\n      ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ =\n        ⟨!![-1, 0; 1, -1], by simp⟩ := by decide\n  have hSTinvMatrix :\n      ModularGroup.S * ModularGroup.T⁻¹ =\n        ⟨!![0, -1; 1, -1], by simp⟩ := by decide\n  have hSTMatrix :\n      ModularGroup.S * ModularGroup.T =\n        ⟨!![0, -1; 1, 1], by simp⟩ := by decide\n  have hTSTMatrix :\n      ModularGroup.T * ModularGroup.S * ModularGroup.T =\n        ⟨!![1, 0; 1, 1], by simp⟩ := by decide\n  have hTinvSMatrix :\n      ModularGroup.T⁻¹ * ModularGroup.S =\n        ⟨!![-1, -1; 1, 0], by simp⟩ := by decide\n  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with\n    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |\n      hSTinv | hST | hTST | hTinvS\n  · exact hcentral\n  all_goals\n    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩\n    rcases hMatrix with rfl | rfl\n    all_goals\n      exfalso\n      have hEntries := CongruenceSubgroup.Gamma_mem.mp hGamma\n      norm_num [ModularGroup.S, ModularGroup.T,\n        hTinvMatrix, hTSMatrix, hTinvSTinvMatrix, hSTinvMatrix, hSTMatrix, hTSTMatrix, hTinvSMatrix] at hEntries\n',
    "gamma": 'theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\n    {gamma : SL(2, ℤ)} {z : ℍ}\n    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)\n    (hz : z ∈ ModularGroup.fd)\n    (hfix : gamma • z = z) :\n    gamma = 1 ∨ gamma = -1 := by\n  have hTinvMatrix :\n      ModularGroup.T⁻¹ =\n        ⟨!![1, -1; 0, 1], by simp⟩ := by decide\n  have hTSMatrix :\n      ModularGroup.T * ModularGroup.S =\n        ⟨!![1, -1; 1, 0], by simp⟩ := by decide\n  have hTinvSTinvMatrix :\n      ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ =\n        ⟨!![-1, 0; 1, -1], by simp⟩ := by decide\n  have hSTinvMatrix :\n      ModularGroup.S * ModularGroup.T⁻¹ =\n        ⟨!![0, -1; 1, -1], by simp⟩ := by decide\n  have hSTMatrix :\n      ModularGroup.S * ModularGroup.T =\n        ⟨!![0, -1; 1, 1], by simp⟩ := by decide\n  have hTSTMatrix :\n      ModularGroup.T * ModularGroup.S * ModularGroup.T =\n        ⟨!![1, 0; 1, 1], by simp⟩ := by decide\n  have hTinvSMatrix :\n      ModularGroup.T⁻¹ * ModularGroup.S =\n        ⟨!![-1, -1; 1, 0], by simp⟩ := by decide\n  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with\n    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |\n      hSTinv | hST | hTST | hTinvS\n  · exact hcentral\n  all_goals\n    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩\n    rcases hMatrix with rfl | rfl\n    all_goals\n      exfalso\n      norm_num [CongruenceSubgroup.Gamma_mem,\n        ModularGroup.S, ModularGroup.T,\n        hTinvMatrix, hTSMatrix, hTinvSTinvMatrix, hSTinvMatrix, hSTMatrix, hTSTMatrix, hTinvSMatrix] at hGamma\n',
    "offdiag": 'theorem gammaTwo_matrix_eq_one_or_neg_one_of_mem_fd_fixed\n    {gamma : SL(2, ℤ)} {z : ℍ}\n    (hGamma : gamma ∈ CongruenceSubgroup.Gamma 2)\n    (hz : z ∈ ModularGroup.fd)\n    (hfix : gamma • z = z) :\n    gamma = 1 ∨ gamma = -1 := by\n  have hTinvMatrix :\n      ModularGroup.T⁻¹ =\n        ⟨!![1, -1; 0, 1], by simp⟩ := by decide\n  have hTSMatrix :\n      ModularGroup.T * ModularGroup.S =\n        ⟨!![1, -1; 1, 0], by simp⟩ := by decide\n  have hTinvSTinvMatrix :\n      ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ =\n        ⟨!![-1, 0; 1, -1], by simp⟩ := by decide\n  have hSTinvMatrix :\n      ModularGroup.S * ModularGroup.T⁻¹ =\n        ⟨!![0, -1; 1, -1], by simp⟩ := by decide\n  have hSTMatrix :\n      ModularGroup.S * ModularGroup.T =\n        ⟨!![0, -1; 1, 1], by simp⟩ := by decide\n  have hTSTMatrix :\n      ModularGroup.T * ModularGroup.S * ModularGroup.T =\n        ⟨!![1, 0; 1, 1], by simp⟩ := by decide\n  have hTinvSMatrix :\n      ModularGroup.T⁻¹ * ModularGroup.S =\n        ⟨!![-1, -1; 1, 0], by simp⟩ := by decide\n  have hUpper :\n      (((gamma 0 1 : ℤ) : ZMod 2)) = 0 :=\n    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.1\n  have hLower :\n      (((gamma 1 0 : ℤ) : ZMod 2)) = 0 :=\n    (CongruenceSubgroup.Gamma_mem.mp hGamma).2.2.1\n  rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz (hfix ▸ hz) with\n    hcentral | hT | hTinv | hS | hTS | hTinvSTinv |\n      hSTinv | hST | hTST | hTinvS\n  · exact hcentral\n  all_goals\n    rcases ‹(_ ∨ _) ∧ _› with ⟨hMatrix, _⟩\n    rcases hMatrix with rfl | rfl\n    all_goals\n      exfalso\n      norm_num [ModularGroup.S, ModularGroup.T,\n        hTinvMatrix, hTSMatrix, hTinvSTinvMatrix, hSTinvMatrix, hSTMatrix, hTSTMatrix, hTinvSMatrix] at hUpper hLower\n',
}

def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_probe39_gamma_two.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant: {variant}")
    path = Path(filename)
    raw = path.read_bytes()
    actual_sha = hashlib.sha256(raw).hexdigest()
    actual_blob = git_blob(raw)
    assert actual_sha == INPUT_SHA256, (actual_sha, INPUT_SHA256)
    assert actual_blob == INPUT_BLOB, (actual_blob, INPUT_BLOB)
    text = raw.decode("utf-8")
    assert text.count(OLD) == 1, text.count(OLD)
    text = text.replace(OLD, VARIANTS[variant], 1)
    path.write_text(text, encoding="utf-8")
    result = path.read_bytes()
    expected = EXPECTED[variant]
    sha256 = hashlib.sha256(result).hexdigest()
    blob = git_blob(result)
    assert sha256 == expected["sha256"], (sha256, expected["sha256"])
    assert blob == expected["blob"], (blob, expected["blob"])
    assert len(result) == expected["bytes"], (len(result), expected["bytes"])
    assert result.count(b"\n") == expected["lf"], (result.count(b"\n"), expected["lf"])
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
        "schema": "qym-probe39-gamma-two-v1",
        "variant": variant,
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
