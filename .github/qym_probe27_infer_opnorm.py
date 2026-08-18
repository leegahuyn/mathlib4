#!/usr/bin/env python3
from pathlib import Path
import hashlib
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
OUTPUT_SHA256 = "c1e3b8e3de022b9eecf03c129cd78fa799a7dd9a1732748032e5711625dceee5"
OUTPUT_BLOB = "be1a2a05a5dfb24b9b18d720a44b2d26cac553d1"

OLD = """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""
NEW = """theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""

path = Path(sys.argv[1])
raw = path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
text = raw.decode("utf-8")
assert text.count(OLD) == 1
text = text.replace(OLD, NEW, 1)
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
