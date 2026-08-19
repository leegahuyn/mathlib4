#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"
# Keep the historical driver-facing name; the commit/run identity marks V10.
VARIANT = "change_pointwise_keep_trace"

FIRST = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by
    simp [g]
  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        (x : ℂ) +
          (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) := by
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.add contDiff_const
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.num,
      actualFixedPhaseHorizontalHorocyclePoint] using
      (contDiff_const.mul hcurve).add contDiff_const
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.denom,
      actualFixedPhaseHorizontalHorocyclePoint] using
      (contDiff_const.mul hcurve).add contDiff_const
  have hden : ∀ x : ℝ,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x) ≠ 0 := by
    intro x
    exact UpperHalfPlane.denom_ne_zero g
      (actualFixedPhaseHorizontalHorocyclePoint Y x)

  have hinvRaw := hdenDiff.inv hden
  change ContDiff ℝ ∞
      (fun x : ℝ =>
        (UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ))⁻¹) at hinvRaw
  have hmulRaw := hnum.mul hinvRaw
  change ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) *
          (UpperHalfPlane.denom g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ))⁻¹) at hmulRaw
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) /
          UpperHalfPlane.denom g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [div_eq_mul_inv] using hmulRaw

  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac
'''

TRACE = r'''theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
    (n : ℤ) (kappa : GammaTwoCusp) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ContDiff ℝ ∞
      (actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u) := by
  have hu : ContDiffOn ℝ ∞
      (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      UpperHalfPlane.upperHalfPlaneSet :=
    (u : SmoothQuotientCompactFunction).1.2
  have hcurve := actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y
  have hcomp := hu.comp_contDiff hcurve
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
  simpa only [actualFixedPhaseNamedCuspTraceRepresentative,
    Function.comp_apply, upperLift_apply] using hcomp
'''

FIRST_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
    r"(?=^/-- Restriction of every actual real-smooth automorphic core section)"
)
TRACE_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff\b.*?"
    r"(?=^/-- Every actual smooth trace is Lipschitz)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "admit": len(re.findall(r"\badmit\b", text)),
        "native_decide": len(re.findall(r"\bnative_decide\b", text)),
        "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
        "maxHeartbeats_zero": len(
            re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)
        ),
    }


def one_match(pattern: re.Pattern[str], text: str, label: str) -> re.Match[str]:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected exactly one {label}, found {len(matches)}")
    return matches[0]


def replace_one(text: str, pattern: re.Pattern[str], replacement: str, label: str) -> str:
    match = one_match(pattern, text, label)
    return text[:match.start()] + replacement.rstrip() + "\n\n" + text[match.end():]


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] != VARIANT:
        raise SystemExit(f"usage: {sys.argv[0]} {VARIANT} QYM.lean")

    path = Path(sys.argv[2])
    before = path.read_bytes()
    if sha256(before) != BASE_SHA256:
        raise SystemExit("unexpected GB85 input SHA256")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("unexpected GB85 input Git blob")

    text = before.decode("utf-8")
    before_audit = audit(text)
    first_before = one_match(FIRST_RE, text, "first C2 producer").group(0)
    trace_before = one_match(TRACE_RE, text, "trace producer").group(0)

    text = replace_one(text, FIRST_RE, FIRST, "first C2 producer")
    text = replace_one(text, TRACE_RE, TRACE, "trace producer")

    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")

    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    marker = "/-- Every actual smooth trace is Lipschitz"
    marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit("could not locate post-C2 gate marker")
    gate_line = text.count("\n", 0, marker_index) + 1

    print(json.dumps({
        "schema": "qym-gb85-c2-v10-patch-v1",
        "variant": VARIANT,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": sha256(after),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": gate_line,
        "replaced_first_sha256": sha256(first_before.encode("utf-8")),
        "replaced_trace_sha256": sha256(trace_before.encode("utf-8")),
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
