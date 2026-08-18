#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
EXPECTED = {
    "exact": {
        "sha256": "f11a70bcdee0640e50d5d8fbba6881a784f2b9196022b19fcf372276aceb05d6",
        "blob": "6fb222d749b2ae4f03dbc3e509f755eb2d86a535",
    },
    "bound": {
        "sha256": "616eed9e72bcf19619f0be206d545c12d7ffbc920479dadeb8696556170c0fb1",
        "blob": "94d0a34dba321cd1f9ad370a5381913349fd519d",
    },
    "rawbound": {
        "sha256": "f6d0fd8b1af77c07bd44572afb18c6cf776dabd3c45af0a0dbe2f4bfd5debdcf",
        "blob": "9e2160773d7a04d25643ab381b776e7c3a98e89b",
    },
}

OLD = """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""

EXPLICIT_NORM = """/- Explicit operator-norm instance for the exact projection map carrier. -/
noncomputable local instance actualFixedPhaseCanonicalTraceClassProjection_normInst
    (n : ℤ) (Y : ℝ) :
    Norm (ActualFixedPhaseCuspTraceCompletion n Y →L[ℂ]
      ActualFixedPhaseCanonicalTraceClass n Y) :=
  @ContinuousLinearMap.hasOpNorm ℂ ℂ
    (ActualFixedPhaseCuspTraceCompletion n Y)
    (ActualFixedPhaseCanonicalTraceClass n Y)
    (ActualFixedPhaseCuspTraceCompletion n Y).normedAddCommGroup
    (ActualFixedPhaseCanonicalTraceClass n Y).normedAddCommGroup
    (inferInstance : NontriviallyNormedField ℂ)
    (inferInstance : NontriviallyNormedField ℂ)
    (ActualFixedPhaseCuspTraceCompletion n Y).normedSpace
    (ActualFixedPhaseCanonicalTraceClass n Y).innerProductSpace.toNormedSpace
    (RingHom.id ℂ)

"""

THEOREMS = {
    "exact": """/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
""",
    "bound": """/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖actualFixedPhaseCanonicalTraceClassProjection n Y‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using actualFixedPhaseCanonicalTraceClassProjection_norm_le n Y x
""",
    "rawbound": """/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (ActualFixedPhaseCanonicalTraceClass n Y).norm_orthogonalProjectionOnto_apply_le x
""",
}

CUT = """/-- Removing the canonical orthogonal representative leaves an element of
"""


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit("usage: SCRIPT VARIANT INPUT OUTPUT")
    variant, input_name, output_name = sys.argv[1:]
    assert variant in EXPECTED
    raw = Path(input_name).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    text = raw.decode("utf-8")
    assert text.count(OLD) == 1
    text = text.replace(OLD, EXPLICIT_NORM + THEOREMS[variant], 1)
    assert text.count(CUT) == 1
    text = text.split(CUT, 1)[0] + "end QYM.FullCertification.P2ClassicalTraceBoundaryExtension\n"
    out = Path(output_name)
    out.write_text(text, encoding="utf-8")
    result = out.read_bytes()
    sha = hashlib.sha256(result).hexdigest()
    blob = git_blob(result)
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
        "schema": "qym-probe33-opnorm-instance-matrix-v1",
        "variant": variant,
        "candidate_sha256": sha,
        "candidate_blob": blob,
        "bytes": len(result),
        "lf": result.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
