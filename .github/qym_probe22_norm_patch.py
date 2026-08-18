#!/usr/bin/env python3
from pathlib import Path
import hashlib
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
OUTPUT_SHA256 = "f832a8ef98f258359d05692f8c8e5a7c28889399744ad21ac05463e6475db636"
OUTPUT_BLOB = "52d9a84110dfeb45a138ab940ac6377dd8bec456"

path = Path(sys.argv[1])
raw = path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
text = raw.decode("utf-8")

anchor = """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Operator norm of the intrinsic trace-class projection is at most one. -/
"""
block = """/-- Explicit operator-norm instance for the exact trace projection map type.
This bypasses the generic typeclass search loop while using the canonical
NormedSpace structures already carried by the domain and codomain. -/
noncomputable local instance (priority := 10000)
    actualFixedPhaseCanonicalTraceClassMapNorm
    (n : ℤ) (Y : ℝ) :
    Norm (ActualFixedPhaseCuspTraceCompletion n Y →L[ℂ]
      ActualFixedPhaseCanonicalTraceClass n Y) := by
  letI : NormedSpace ℂ (ActualFixedPhaseCuspTraceCompletion n Y) :=
    (ActualFixedPhaseCuspTraceCompletion n Y).normedSpace
  letI : NormedSpace ℂ (ActualFixedPhaseCanonicalTraceClass n Y) :=
    (ActualFixedPhaseCanonicalTraceClass n Y).innerProductSpace.toNormedSpace
  exact ContinuousLinearMap.hasOpNorm

"""
assert text.count(anchor) == 1
text = text.replace(anchor, block + anchor, 1)
path.write_text(text, encoding="utf-8")
result = path.read_bytes()
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
