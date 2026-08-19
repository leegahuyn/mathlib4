#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"
VARIANTS = {
    "ofreal_apply_mulinv_simpa",
    "ofreal_apply_mulinv_rw",
    "ofreal_apply_mulinv_change",
}

REGION_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
    r"(?=^/-- Every actual smooth trace is Lipschitz)"
)


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


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


FIRST_PREFIX = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  let sigma : SL(2, ℤ) := gammaTwoCuspScaling kappa
  have hcurve0 : ContDiff ℝ ∞
      (fun x : ℝ =>
        Complex.ofRealCLM x +
          (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.add contDiff_const
  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [actualFixedPhaseHorizontalHorocyclePoint,
      Complex.ofRealCLM_apply] using hcurve0
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) :=
    ((contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 0 0) : ℂ))).mul hcurve).add
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 0 1) : ℂ)))
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) :=
    ((contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 1 0) : ℂ))).mul hcurve).add
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 1 1) : ℂ)))
  have hden : ∀ x : ℝ,
      ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
        (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) ≠ 0 := by
    intro x
    simpa [UpperHalfPlane.denom, sigma] using
      (UpperHalfPlane.denom_ne_zero
        ((gammaTwoCuspScaling kappa : SL(2, ℤ)) : GL (Fin 2) ℝ)
        (actualFixedPhaseHorizontalHorocyclePoint Y x))
  have hinv : ContDiff ℝ ∞
      (fun x : ℝ =>
        ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ))⁻¹) :=
    hdenDiff.inv hden
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        ((algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) *
        ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ))⁻¹) :=
    hnum.mul hinv
'''

FIRST_ENDINGS = {
    "ofreal_apply_mulinv_simpa": r'''  simpa only [actualFixedPhaseCuspHorocyclePoint, sigma,
    UpperHalfPlane.coe_specialLinearGroup_apply, div_eq_mul_inv] using hfrac
''',
    "ofreal_apply_mulinv_rw": r'''  simp only [actualFixedPhaseCuspHorocyclePoint, sigma,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  rw [show
      (fun x : ℝ =>
        (((algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 0 0) : ℂ) *
              (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
            (algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 0 1) : ℂ)) /
          ((algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 1 0) : ℂ) *
              (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
            (algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 1 1) : ℂ)))) =
      (fun x : ℝ =>
        ((algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 0 0) : ℂ) *
              (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
            (algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 0 1) : ℂ)) *
          ((algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 1 0) : ℂ) *
              (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
            (algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 1 1) : ℂ))⁻¹) by
        funext x
        exact div_eq_mul_inv _ _]
  simpa only [sigma] using hfrac
''',
    "ofreal_apply_mulinv_change": r'''  simp only [actualFixedPhaseCuspHorocyclePoint, sigma,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      ((algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 0 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 0 1) : ℂ)) *
        ((algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ ((gammaTwoCuspScaling kappa) 1 1) : ℂ))⁻¹)
  simpa only [sigma] using hfrac
''',
}

SECOND_SIMPA = r'''

/-- Restriction of every actual real-smooth automorphic core section to a
named cusp horocycle is a real `C-infinity` function of the boundary
parameter. -/
theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
    (n : ℤ) (kappa : GammaTwoCusp) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ContDiff ℝ ∞
      (actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u) := by
  have hu : ContDiffOn ℝ ∞
      (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ))
      UpperHalfPlane.upperHalfPlaneSet :=
    (u : SmoothQuotientCompactFunction).1.2
  have hcomp := hu.comp_contDiff
    (actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y)
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
  simpa [actualFixedPhaseNamedCuspTraceRepresentative,
    upperLift, Function.comp_def] using hcomp
'''

SECOND_CHANGE = r'''

/-- Restriction of every actual real-smooth automorphic core section to a
named cusp horocycle is a real `C-infinity` function of the boundary
parameter. -/
theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
    (n : ℤ) (kappa : GammaTwoCusp) (Y : ℝ)
    (u : InverseEtaFixedPhaseCore n) :
    ContDiff ℝ ∞
      (actualFixedPhaseNamedCuspTraceRepresentative n kappa Y u) := by
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ)
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ))
  exact (u : SmoothQuotientCompactFunction).1.2.comp_contDiff
    (actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y)
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
'''

SECOND_ORIGINAL_SHAPE = r'''

/-- Restriction of every actual real-smooth automorphic core section to a
named cusp horocycle is a real `C-infinity` function of the boundary
parameter. -/
theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
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
  change ContDiff ℝ ∞
    (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘
      fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ))
  exact hcomp
'''

SECOND_BY_VARIANT = {
    "ofreal_apply_mulinv_simpa": SECOND_SIMPA,
    "ofreal_apply_mulinv_rw": SECOND_CHANGE,
    "ofreal_apply_mulinv_change": SECOND_ORIGINAL_SHAPE,
}


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit(
            "usage: qym_patch_gb85_c2_mulinv_v6.py VARIANT QYM.lean"
        )
    variant = sys.argv[1]
    path = Path(sys.argv[2])
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("GB85 SHA256 mismatch")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("GB85 Git blob mismatch")

    text = before.decode("utf-8")
    matches = list(REGION_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"C2 region count={len(matches)}")
    replacement = (
        FIRST_PREFIX + FIRST_ENDINGS[variant] + SECOND_BY_VARIANT[variant]
    ).rstrip()
    match = matches[0]
    after_text = text[:match.start()] + replacement + "\n\n" + text[match.end():]
    before_audit = audit(text)
    after_audit = audit(after_text)
    if before_audit != after_audit:
        raise SystemExit(f"forbidden delta {before_audit}->{after_audit}")

    path.write_text(after_text, encoding="utf-8")
    after = path.read_bytes()
    marker = "/-- Every actual smooth trace is Lipschitz"
    marker_index = after_text.find(marker)
    if marker_index < 0:
        raise SystemExit("post-C2 gate marker missing")

    print(json.dumps({
        "schema": "qym-gb85-c2-mulinv-v6",
        "variant": variant,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": after_text.count("\n", 0, marker_index) + 1,
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
