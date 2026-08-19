#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"

# ASCII-only Python source: Unicode Lean symbols are emitted through escapes.
REPLACEMENT = """theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : \u211d) :
    ContDiff \u211d \u221e
      (fun x : \u211d =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : \u210d) : \u2102)) := by
  let g : GL (Fin 2) \u211d :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) \u211d)
  have hg : 0 < g.det.val := by
    simp [g]
  have hcurve : ContDiff \u211d \u221e
      (fun x : \u211d =>
        (x : \u2102) +
          (actualFixedPhaseCuspHeight Y : \u2102) * Complex.I) := by
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.add contDiff_const
  have hnum : ContDiff \u211d \u221e
      (fun x : \u211d =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : \u2102)) := by
    simpa only [UpperHalfPlane.num,
      actualFixedPhaseHorizontalHorocyclePoint] using
      (contDiff_const.mul hcurve).add contDiff_const
  have hdenDiff : ContDiff \u211d \u221e
      (fun x : \u211d =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : \u2102)) := by
    simpa only [UpperHalfPlane.denom,
      actualFixedPhaseHorizontalHorocyclePoint] using
      (contDiff_const.mul hcurve).add contDiff_const
  have hden : \u2200 x : \u211d,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x) \u2260 0 := by
    intro x
    exact UpperHalfPlane.denom_ne_zero g
      (actualFixedPhaseHorizontalHorocyclePoint Y x)
  have hfrac : ContDiff \u211d \u221e
      (fun x : \u211d =>
        UpperHalfPlane.num g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : \u2102) /
          UpperHalfPlane.denom g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : \u2102)) :=
    hnum.div hdenDiff hden
  change ContDiff \u211d \u221e
    (fun x : \u211d =>
      (\u2191(g \u2022 actualFixedPhaseHorizontalHorocyclePoint Y x) : \u2102))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac

/-- Restriction of every actual real-smooth automorphic core section to a
named cusp horocycle is a real `C-infinity` function of the boundary
parameter. -/
theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
    (n : \u2124) (kappa : GammaTwoCusp) (Y : \u211d)
    (u : InverseEtaFixedPhaseCore n) :
    ContDiff \u211d \u221e
      (actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u) := by
  have hu : ContDiffOn \u211d \u221e
      (upperLift ((u : SmoothQuotientCompactFunction) : \u210d \u2192 \u2102))
      UpperHalfPlane.upperHalfPlaneSet :=
    (u : SmoothQuotientCompactFunction).1.2
  have hcurve := actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y
  have hcomp := hu.comp_contDiff hcurve
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
  simpa only [actualFixedPhaseNamedCuspTraceRepresentative,
    Function.comp_apply, upperLift_apply] using hcomp
"""

PATTERN = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
    r"(?=^/-- Every actual smooth trace is Lipschitz)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode() + b"\0" + data
    ).hexdigest()


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_c2_gb85_v3.py QYM.lean OUTDIR")
    path = Path(sys.argv[1])
    out = Path(sys.argv[2])
    out.mkdir(parents=True, exist_ok=True)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("unexpected GB85 SHA256")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("unexpected GB85 blob")
    text = before.decode("utf-8")
    text, count = PATTERN.subn(REPLACEMENT.rstrip() + "\n\n", text)
    if count != 1:
        raise SystemExit(f"expected one C2 block, found {count}")
    marker = text.index("/-- Every actual smooth trace is Lipschitz")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
    }
    if any(forbidden.values()):
        raise SystemExit(f"forbidden audit failed: {forbidden}")
    result = {
        "schema": "qym-c2-gb85-v3",
        "baseline_sha256": BASE_SHA256,
        "baseline_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": text.count("\n", 0, marker) + 1,
        "forbidden": forbidden,
    }
    (out / "PATCH_RESULT.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n"
    )
    (out / "QYM.candidate-C2.lean").write_bytes(after)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
