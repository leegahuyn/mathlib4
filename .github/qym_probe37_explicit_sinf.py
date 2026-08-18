#!/usr/bin/env python3
from pathlib import Path
import hashlib
import re
import sys

INPUT_SHA256 = "5b944b2332e3d0aa2816009a0cd1c8eb172bbb0861cb5e387c2ce26c6aeb3094"
PREFIX_SHA256 = "1fce4f041ca76a27c317706909ca044f28254a24a68e2055fe3534312ef57812"
PREFIX_BLOB = "831d2805022f79b544762b3498805e04ec46d23d"
FULL_SHA256 = "54a1861c5cb9b35ca5f71c6665a76b3d4f76a3d75a4b01a37242f70005603638"
FULL_BLOB = "ad278b20db3aaecf5ec693efcacd4a4a45af9095"

OLD = """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""
NEW = """/-- Operator norm of the intrinsic trace-class projection is at most one.
This is the defining `sInf` formula for the operator norm, written explicitly
so that the statement does not depend on an ambiguous map-space `Norm` instance. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    sInf {c : ℝ | 0 ≤ c ∧ ∀ x : ActualFixedPhaseCuspTraceCompletion n Y,
      ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto x‖ ≤
        c * ‖x‖} ≤ 1 := by
  apply csInf_le
  · exact ⟨0, fun _ hc => hc.1⟩
  · exact ⟨zero_le_one, fun x => by
      simpa using
        (ActualFixedPhaseCanonicalTraceClass n Y).norm_orthogonalProjectionOnto_apply_le x⟩
"""
CUT = """/-- Removing the canonical orthogonal representative leaves an element of
"""

mode, input_name, output_name = sys.argv[1:]
assert mode in {"prefix", "full"}
raw = Path(input_name).read_bytes()
assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
text = raw.decode("utf-8")
assert text.count(OLD) == 1
text = text.replace(OLD, NEW, 1)
if mode == "prefix":
    assert text.count(CUT) == 1
    text = text.split(CUT, 1)[0] + "end QYM.FullCertification.P2ClassicalTraceBoundaryExtension\n"
out = Path(output_name)
out.write_text(text, encoding="utf-8")
result = out.read_bytes()
sha = hashlib.sha256(result).hexdigest()
blob = hashlib.sha1(b"blob " + str(len(result)).encode() + b"\0" + result).hexdigest()
if mode == "prefix":
    assert sha == PREFIX_SHA256 and blob == PREFIX_BLOB, (sha, blob)
else:
    assert sha == FULL_SHA256 and blob == FULL_BLOB, (sha, blob)

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
print(sha)
print(blob)
