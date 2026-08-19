#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"
VARIANTS = {"function_eq", "convert", "unfold_action"}
REGION_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
    r"(?=^/-- Every actual smooth trace is Lipschitz)"
)


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def audit(text: str) -> dict[str, int]:
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"Lean\.ofReduceBool",
        "global_axiom": r"(?m)^\s*axiom\s+",
        "unsafe": r"(?m)^\s*unsafe\s+",
        "maxHeartbeats_zero": r"set_option\s+maxHeartbeats\s+0\b",
    }
    return {name: len(re.findall(pattern, text)) for name, pattern in patterns.items()}


PREFIX = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
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
    simpa only [UpperHalfPlane.denom, sigma] using
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

ENDINGS = {
    "function_eq": r'''  have hfun :
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) =
      (fun x : ℝ =>
        ((algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) *
        ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ))⁻¹) := by
    funext x
    simp only [actualFixedPhaseCuspHorocyclePoint,
      UpperHalfPlane.coe_specialLinearGroup_apply, div_eq_mul_inv, sigma]
  rw [hfun]
  exact hfrac
''',
    "convert": r'''  convert hfrac using 1 <;>
    simp only [actualFixedPhaseCuspHorocyclePoint,
      UpperHalfPlane.coe_specialLinearGroup_apply, div_eq_mul_inv, sigma]
''',
    "unfold_action": r'''  simp only [actualFixedPhaseCuspHorocyclePoint]
  rw [show
      (fun x : ℝ =>
        ((((gammaTwoCuspScaling kappa) : SL(2, ℤ)) •
          actualFixedPhaseHorizontalHorocyclePoint Y x : ℍ) : ℂ)) =
      (fun x : ℝ =>
        ((algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) *
        ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ))⁻¹) by
      funext x
      simp only [UpperHalfPlane.coe_specialLinearGroup_apply,
        div_eq_mul_inv, sigma]]
  exact hfrac
''',
}

SECOND = r'''

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
  simpa only [actualFixedPhaseNamedCuspTraceRepresentative,
    upperLift, Function.comp_def] using hcomp
'''


def main() -> None:
    if len(sys.argv) != 4 or sys.argv[1] not in VARIANTS:
        raise SystemExit("usage: fallback.py VARIANT INPUT OUTPUT")
    variant = sys.argv[1]
    source = Path(sys.argv[2])
    output = Path(sys.argv[3])
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != BASE_SHA256 or git_blob(raw) != BASE_BLOB:
        raise SystemExit("immutable GB85 mismatch")
    text = raw.decode("utf-8")
    matches = list(REGION_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"region count={len(matches)}")
    replacement = (PREFIX + ENDINGS[variant] + SECOND).rstrip()
    match = matches[0]
    after = text[:match.start()] + replacement + "\n\n" + text[match.end():]
    if audit(after) != audit(text):
        raise SystemExit("forbidden-token delta")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(after, encoding="utf-8")
    marker = "/-- Every actual smooth trace is Lipschitz"
    gate_index = after.find(marker)
    if gate_index < 0:
        raise SystemExit("gate marker missing")
    data = output.read_bytes()
    print(json.dumps({
        "variant": variant,
        "candidate_qym_sha256": hashlib.sha256(data).hexdigest(),
        "candidate_qym_blob": git_blob(data),
        "gate_line": after.count("\n", 0, gate_index) + 1,
        "forbidden": audit(after),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
