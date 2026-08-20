#!/usr/bin/env python3
from pathlib import Path
import hashlib
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
OUTPUT_SHA256 = "42adb9169ac6c7c924a99813306b85fc49dd5cb69ec24c812ed4cb73f6c9dcb0"
OUTPUT_BLOB = "f6263e00a11a1adb910a937646eb8e5f0e2ec22c"

OLD_OPNORM = """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖(ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto‖ ≤ 1 :=
  (ActualFixedPhaseCanonicalTraceClass n Y).orthogonalProjectionOnto_norm_le
"""
NEW_OPNORM = """/-- Explicit operator-norm structure for this fixed continuous-linear-map type.
It is the standard infimum of all nonnegative pointwise bounds, written directly
to avoid an ambiguous `NormedSpace.toModule` search for the subtype codomain. -/
noncomputable local instance (priority := 2000)
    actualFixedPhaseCanonicalTraceClassProjectionNorm
    (n : ℤ) (Y : ℝ) :
    Norm
      (ActualFixedPhaseCuspTraceCompletion n Y →L[ℂ]
        ActualFixedPhaseCanonicalTraceClass n Y) where
  norm f := sInf {c : ℝ | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}

/-- Operator norm of the intrinsic trace-class projection is at most one. -/
theorem actualFixedPhaseCanonicalTraceClassProjection_opNorm_le
    (n : ℤ) (Y : ℝ) :
    ‖actualFixedPhaseCanonicalTraceClassProjection n Y‖ ≤ 1 := by
  refine csInf_le ?_ ?_
  · exact ⟨0, fun c hc => hc.1⟩
  · exact ⟨zero_le_one, fun x => by
      simpa using actualFixedPhaseCanonicalTraceClassProjection_norm_le n Y x⟩
"""

OLD_HHALF = """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  inferInstance
"""
NEW_HHALF = """noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  (ActualFixedPhaseHhalfTraceCompletion n Y).innerProductSpace
"""

path = Path(sys.argv[1])
raw = path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
text = raw.decode("utf-8")
assert text.count(OLD_OPNORM) == 1
assert text.count(OLD_HHALF) == 1
text = text.replace(OLD_OPNORM, NEW_OPNORM, 1)
text = text.replace(OLD_HHALF, NEW_HHALF, 1)
path.write_text(text, encoding="utf-8")
result = path.read_bytes()
sha = hashlib.sha256(result).hexdigest()
blob = hashlib.sha1(b"blob " + str(len(result)).encode() + b"\0" + result).hexdigest()
assert sha == OUTPUT_SHA256, sha
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
print(f"sha256={sha}")
print(f"blob={blob}")
print(f"bytes={len(result)}")
print(f"lf={result.count(b'\n')}")
