#!/usr/bin/env python3
from pathlib import Path
import hashlib
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
OUTPUT_SHA256 = "6317b7082a71c3c6ef0fcdf56015a2561f15619546aa34384e0fd845fc9f2335"
OUTPUT_BLOB = "26429e48400395468ec4d827ad6112b6f6df2beb"

OLD = """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""
NEW = """/- The exact operator norm on the intrinsic projection carrier. -/
noncomputable local instance actualFixedPhaseCanonicalTraceClassProjectionNorm
    (n : ℤ) (Y : ℝ) :
    Norm (ActualFixedPhaseCuspTraceCompletion n Y →L[ℂ]
      ActualFixedPhaseCanonicalTraceClass n Y) :=
  ⟨fun f => sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}⟩

/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 := by
  change sInf {c : ℝ | 0 ≤ c ∧ ∀ x,
      ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto x‖ ≤
        c * ‖x‖} ≤ 1
  apply csInf_le
  · exact ⟨0, fun _ hc => hc.1⟩
  · constructor
    · exact zero_le_one
    · intro x
      simpa using
        (ActualFixedPhaseCanonicalTraceClass n Y).norm_orthogonalProjectionOnto_apply_le x
"""
CUT = """/-- Removing the canonical orthogonal representative leaves an element of
"""

src = Path(sys.argv[1]).read_bytes()
assert hashlib.sha256(src).hexdigest() == INPUT_SHA256
text = src.decode("utf-8")
assert text.count(OLD) == 1
assert text.count(CUT) == 1
text = text.replace(OLD, NEW, 1)
text = text.split(CUT, 1)[0] + "end QYM.FullCertification.P2ClassicalTraceBoundaryExtension\n"
out = Path(sys.argv[2])
out.write_text(text, encoding="utf-8")
result = out.read_bytes()
assert hashlib.sha256(result).hexdigest() == OUTPUT_SHA256
blob = hashlib.sha1(b"blob " + str(len(result)).encode() + b"\0" + result).hexdigest()
assert blob == OUTPUT_BLOB, blob

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
print(OUTPUT_SHA256)
