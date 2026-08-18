#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
EXPECTED = {
    "norm-num": {
        "sha256": "443f2395357537bf6927f87e9be64d1d4e5b02450b11c271dfa95c8f9aacd60a",
        "blob": "b12d2904854c801ae604d5febcb4de6c0d56baf9",
    },
    "simp-pow": {
        "sha256": "ed4f0ab98cb780906691149fd2e784e6fe6fd65a8b14689722dddac0eea4d220",
        "blob": "1985681fc758174697f02f024374892c8e4fa893",
    },
    "norm-cast": {
        "sha256": "91ca74c018d50ae83631c338eef4ab624ccd322c7a2aebe683965c07e7c8cdb6",
        "blob": "66b46235eb4cfcfcad7ea1db1da44da2771130c7",
    },
}

COMMON_REPLACEMENTS = [
    (
        """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
""",
        """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) : _ :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
""",
    ),
    (
        """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  inferInstance
""",
        """noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  (ActualFixedPhaseHhalfTraceCompletion n Y).innerProductSpace
""",
    ),
    (
        """  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem, huv]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, add_zero]
""",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionRepresentative, hx, huv]
  · simp [globalStageProjectionRepresentative, hx]
""",
    ),
    (
        """  by_cases hx : x ∈ naturalStageSet n
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_mem, hcu]
  · simp only [globalStageProjectionRepresentative, hx,
      Set.indicator_of_notMem, smul_zero]
""",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionRepresentative, hx, hcu]
  · simp [globalStageProjectionRepresentative, hx]
""",
    ),
    (
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative, hx]
""",
        """  by_cases hx : x ∈ naturalStageSet n
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative,
      naturalStageSet, naturalStageCutoff, hx]
  · simp [globalStageProjectionErrorDensity,
      globalL2DominatingDensity,
      globalStageProjectionRepresentative,
      naturalStageSet, naturalStageCutoff, hx]
""",
    ),
    (
        """  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hn]
""",
        """  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative,
    naturalStageSet, naturalStageCutoff, hn]
""",
    ),
    (
        """  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative, hx]
""",
        """  simp [globalStageProjectionErrorDensity,
    globalStageProjectionRepresentative,
    naturalStageSet, naturalStageCutoff, hx]
""",
    ),
    (
        """  simpa only [coordinateFriedrichsHamiltonian] using
    QYM.RCLikeCoerciveFormFriedrichsExtension.realization_hasCompactResolventAt_negShift
""",
        """  simpa [coordinateFriedrichsHamiltonian] using
    QYM.RCLikeCoerciveFormFriedrichsExtension.realization_hasCompactResolventAt_negShift
""",
    ),
]

OLD_COORD = """  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp
"""
COORD_VARIANTS = {
    "norm-num": """  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_num
""",
    "simp-pow": """  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp [map_pow]
""",
    "norm-cast": """  rw [coordinateHamiltonianForm_apply,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  norm_cast
""",
}


def replace_once(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, (old[:100], text.count(old))
    return text.replace(old, new, 1)


def main() -> None:
    variant, file_name = sys.argv[1], sys.argv[2]
    assert variant in EXPECTED
    path = Path(file_name)
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    text = raw.decode("utf-8")
    for old, new in COMMON_REPLACEMENTS:
        text = replace_once(text, old, new)
    text = replace_once(text, OLD_COORD, COORD_VARIANTS[variant])
    path.write_text(text, encoding="utf-8")
    result = path.read_bytes()
    sha = hashlib.sha256(result).hexdigest()
    blob = hashlib.sha1(b"blob " + str(len(result)).encode() + b"\0" + result).hexdigest()
    assert sha == EXPECTED[variant]["sha256"], (sha, EXPECTED[variant]["sha256"])
    assert blob == EXPECTED[variant]["blob"], (blob, EXPECTED[variant]["blob"])
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
        "schema": "qym-probe32-tail-matrix-v1",
        "variant": variant,
        "candidate_sha256": sha,
        "candidate_blob": blob,
        "bytes": len(result),
        "lf": result.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
