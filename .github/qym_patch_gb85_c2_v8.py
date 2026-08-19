#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"

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

TRACE_HFUN_FORWARD = r'''theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
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
  have hfun :
      (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘
          fun x : ℝ =>
            ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) =
        actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u := by
    funext x
    change
      upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
          ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ) =
        (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (actualFixedPhaseCuspHorocyclePoint kappa Y x))
    exact upperLift_apply _ _
  exact hfun ▸ hcomp
'''

TRACE_HFUN_REWRITE = r'''theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
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
  have hfun :
      actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u =
        (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘
          fun x : ℝ =>
            ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
    funext x
    change
      (((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
          (actualFixedPhaseCuspHorocyclePoint kappa Y x)) =
        upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
          ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)
    exact (upperLift_apply _ _).symm
  rw [hfun]
  exact hcomp
'''

TRACE_HFUN_SIMPA = r'''theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
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
  have hfun :
      actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u =
        (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘
          fun x : ℝ =>
            ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
    funext x
    simp only [actualFixedPhaseNamedCuspTraceRepresentative,
      Function.comp_apply, upperLift_apply]
  rw [hfun]
  exact hcomp
'''

VARIANTS = {
    "convert_direct": TRACE_HFUN_FORWARD,
    "convert_staged": TRACE_HFUN_REWRITE,
    "change_pointwise": TRACE_HFUN_SIMPA,
}

FIRST_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
    r"(?=^/-- Restriction of every actual real-smooth automorphic core section)"
)
SECOND_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff\b.*?"
    r"(?=^/-- Every actual smooth trace is Lipschitz)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


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


def replace_one(pattern: re.Pattern[str], replacement: str, text: str, label: str) -> str:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected exactly one {label}, found {len(matches)}")
    match = matches[0]
    return text[: match.start()] + replacement.rstrip() + "\n\n" + text[match.end() :]


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb85_c2_v8.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant {variant!r}; expected one of {sorted(VARIANTS)}")

    path = Path(filename)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("unexpected GB85 input SHA256")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("unexpected GB85 input Git blob")

    text = before.decode("utf-8")
    before_audit = audit(text)
    text = replace_one(FIRST_RE, FIRST, text, "first C2 producer")
    text = replace_one(SECOND_RE, VARIANTS[variant], text, "second C2 producer")
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")

    after = path.read_bytes()
    decoded = after.decode("utf-8")
    marker = "/-- Every actual smooth trace is Lipschitz"
    marker_index = decoded.find(marker)
    if marker_index < 0:
        raise SystemExit("could not locate post-C2 gate marker")
    gate_line = decoded.count("\n", 0, marker_index) + 1

    print(json.dumps({
        "schema": "qym-gb85-c2-v10-trace-function-equality-patch-v1",
        "variant": variant,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": gate_line,
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
