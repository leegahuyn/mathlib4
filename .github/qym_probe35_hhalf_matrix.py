#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re
import sys

INPUT_SHA256 = "94fceba9313ded915c6e50a17e156699eb48170595b062b1138d04b6abe31534"
EXPECTED = {
    "flat_named": ("00f2c8ba7fc0329b04ae67c5a67b5814f8118b14222a7831a0401c9d3d374e53", "ee2faeaf281215b0e9b304a96ccdce3e8cdc0ffb"),
    "flat_infer": ("313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e", "ff49510790dd7ca136bf34c3ec7150617ee1c241"),
    "helpers_named": ("77a79855bb35d892579b6331cef613e2c69c0161196c80fddefda795531eb781", "badaa29632997a198493a07762e6f9349bcd1e66"),
}

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
OLD_FRIEDRICHS = """  simpa only [coordinateFriedrichsHamiltonian] using
    QYM.RCLikeCoerciveFormFriedrichsExtension.realization_hasCompactResolventAt_negShift
"""
NEW_FRIEDRICHS = """  simpa [coordinateFriedrichsHamiltonian] using
    QYM.RCLikeCoerciveFormFriedrichsExtension.realization_hasCompactResolventAt_negShift
"""
OLD_HHALF = """set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 2000000 in
noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) :=
  inferInstance
"""

FLAT_NAMED = """noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) := by
  letI : InnerProductSpace ℂ
      (ActualFixedPhaseNamedCuspBoundaryHhalf n .zero Y) :=
    widthTwoHhalfCompletionInnerProductSpace
      (actualFixedPhaseCuspBoundaryTransition n .zero Y)
  letI : InnerProductSpace ℂ
      (ActualFixedPhaseNamedCuspBoundaryHhalf n .one Y) :=
    widthTwoHhalfCompletionInnerProductSpace
      (actualFixedPhaseCuspBoundaryTransition n .one Y)
  letI : InnerProductSpace ℂ
      (WithLp 2
        (ActualFixedPhaseNamedCuspBoundaryHhalf n .zero Y ×
          ActualFixedPhaseNamedCuspBoundaryHhalf n .one Y)) :=
    WithLp.instProdInnerProductSpace
  letI : InnerProductSpace ℂ
      (ActualFixedPhaseNamedCuspBoundaryHhalf n .atInfinity Y) :=
    widthTwoHhalfCompletionInnerProductSpace
      (actualFixedPhaseCuspBoundaryTransition n .atInfinity Y)
  letI : InnerProductSpace ℂ
      (ActualFixedPhaseThreeCuspBoundaryHhalf n Y) :=
    WithLp.instProdInnerProductSpace
  letI : InnerProductSpace ℂ (GraphSobolevCompletion n) := inferInstance
  letI : InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceAmbient n Y) :=
    WithLp.instProdInnerProductSpace
  exact (ActualFixedPhaseHhalfTraceCompletion n Y).innerProductSpace
"""

FLAT_INFER = FLAT_NAMED.replace(":=\n    WithLp.instProdInnerProductSpace", ":= inferInstance")

HELPERS_NAMED = """noncomputable def actualFixedPhaseZeroOneCuspBoundaryHhalfInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ
      (WithLp 2
        (ActualFixedPhaseNamedCuspBoundaryHhalf n .zero Y ×
          ActualFixedPhaseNamedCuspBoundaryHhalf n .one Y)) := by
  letI : InnerProductSpace ℂ
      (ActualFixedPhaseNamedCuspBoundaryHhalf n .zero Y) :=
    widthTwoHhalfCompletionInnerProductSpace
      (actualFixedPhaseCuspBoundaryTransition n .zero Y)
  letI : InnerProductSpace ℂ
      (ActualFixedPhaseNamedCuspBoundaryHhalf n .one Y) :=
    widthTwoHhalfCompletionInnerProductSpace
      (actualFixedPhaseCuspBoundaryTransition n .one Y)
  exact WithLp.instProdInnerProductSpace

noncomputable def actualFixedPhaseThreeCuspBoundaryHhalfInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseThreeCuspBoundaryHhalf n Y) := by
  letI : InnerProductSpace ℂ
      (ActualFixedPhaseNamedCuspBoundaryHhalf n .atInfinity Y) :=
    widthTwoHhalfCompletionInnerProductSpace
      (actualFixedPhaseCuspBoundaryTransition n .atInfinity Y)
  letI : InnerProductSpace ℂ
      (WithLp 2
        (ActualFixedPhaseNamedCuspBoundaryHhalf n .zero Y ×
          ActualFixedPhaseNamedCuspBoundaryHhalf n .one Y)) :=
    actualFixedPhaseZeroOneCuspBoundaryHhalfInnerProductSpace n Y
  exact WithLp.instProdInnerProductSpace

noncomputable def actualFixedPhaseHhalfTraceAmbientInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceAmbient n Y) := by
  letI : InnerProductSpace ℂ (GraphSobolevCompletion n) := inferInstance
  letI : InnerProductSpace ℂ
      (ActualFixedPhaseThreeCuspBoundaryHhalf n Y) :=
    actualFixedPhaseThreeCuspBoundaryHhalfInnerProductSpace n Y
  exact WithLp.instProdInnerProductSpace

noncomputable def actualFixedPhaseHhalfTraceCompletionInnerProductSpace
    (n : ℤ) (Y : ℝ) :
    InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceCompletion n Y) := by
  letI : InnerProductSpace ℂ (ActualFixedPhaseHhalfTraceAmbient n Y) :=
    actualFixedPhaseHhalfTraceAmbientInnerProductSpace n Y
  exact (ActualFixedPhaseHhalfTraceCompletion n Y).innerProductSpace
"""
VARIANTS = {"flat_named": FLAT_NAMED, "flat_infer": FLAT_INFER, "helpers_named": HELPERS_NAMED}


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> None:
    variant, source = sys.argv[1], Path(sys.argv[2])
    assert variant in VARIANTS
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    text = raw.decode("utf-8")
    for old, new in ((OLD_OPNORM, NEW_OPNORM), (OLD_FRIEDRICHS, NEW_FRIEDRICHS),
                     (OLD_HHALF, VARIANTS[variant])):
        assert text.count(old) == 1, (variant, text.count(old), old[:80])
        text = text.replace(old, new, 1)
    source.write_text(text, encoding="utf-8")
    result = source.read_bytes()
    sha, blob = hashlib.sha256(result).hexdigest(), blob_sha(result)
    assert (sha, blob) == EXPECTED[variant], (variant, sha, blob)
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
    print(json.dumps({"variant": variant, "sha256": sha, "blob": blob,
                      "bytes": len(result), "lf": result.count(b"\n"),
                      "forbidden": forbidden}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
