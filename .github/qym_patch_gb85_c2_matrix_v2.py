#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"

HEADER = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by'''

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
  have hcurve := actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y
  have hcomp := hu.comp_contDiff hcurve
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
  simpa [actualFixedPhaseNamedCuspTraceRepresentative,
    upperLift, Function.comp_def] using hcomp
'''

CURVE = r'''
  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        (x : ℂ) +
          (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) := by
    simpa [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ =>
            (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I))
'''

COEFFICIENTS = r'''
  let a : ℂ := g 0 0
  let b : ℂ := g 0 1
  let c : ℂ := g 1 0
  let d : ℂ := g 1 1
  have ha : ContDiff ℝ ∞ (fun _ : ℝ => a) := contDiff_const
  have hb : ContDiff ℝ ∞ (fun _ : ℝ => b) := contDiff_const
  have hc : ContDiff ℝ ∞ (fun _ : ℝ => c) := contDiff_const
  have hd : ContDiff ℝ ∞ (fun _ : ℝ => d) := contDiff_const
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    have hraw : ContDiff ℝ ∞
        (fun x : ℝ =>
          a * ((x : ℂ) +
            (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) + b) :=
      (ha.mul hcurve).add hb
    simpa [a, b, UpperHalfPlane.num,
      actualFixedPhaseHorizontalHorocyclePoint] using hraw
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    have hraw : ContDiff ℝ ∞
        (fun x : ℝ =>
          c * ((x : ℂ) +
            (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) + d) :=
      (hc.mul hcurve).add hd
    simpa [c, d, UpperHalfPlane.denom,
      actualFixedPhaseHorizontalHorocyclePoint] using hraw
  have hden : ∀ x : ℝ,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) ≠ 0 := by
    intro x
    simpa using
      (UpperHalfPlane.denom_ne_zero g
        (actualFixedPhaseHorizontalHorocyclePoint Y x))
'''

PREFIX = HEADER + r'''
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by
    simp [g]
''' + CURVE + COEFFICIENTS

VARIANTS = {
    "coeff_div": PREFIX + r'''
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) /
          UpperHalfPlane.denom g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) :=
    hnum.div hdenDiff hden
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac
''' + SECOND,
    "coeff_mul_inv": PREFIX + r'''
  have hinv : ContDiff ℝ ∞
      (fun x : ℝ =>
        (UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ))⁻¹) :=
    hdenDiff.inv hden
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) *
          (UpperHalfPlane.denom g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ))⁻¹) :=
    hnum.mul hinv
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg, div_eq_mul_inv] using hfrac
''' + SECOND,
    "sl_explicit_div": HEADER + r'''
  let sigma : SL(2, ℤ) := gammaTwoCuspScaling kappa
''' + CURVE + r'''
  have hden : ∀ x : ℝ,
      ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
        (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) ≠ 0 := by
    intro x
    simpa [UpperHalfPlane.denom, sigma] using
      (UpperHalfPlane.denom_ne_zero
        ((gammaTwoCuspScaling kappa : SL(2, ℤ)) : GL (Fin 2) ℝ)
        (actualFixedPhaseHorizontalHorocyclePoint Y x))
  simp only [actualFixedPhaseCuspHorocyclePoint,
    actualFixedPhaseHorizontalHorocyclePoint,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  apply ContDiff.div
  · exact
      ((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ =>
            (algebraMap ℤ ℝ (sigma 0 0) : ℂ))).mul hcurve).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ =>
            (algebraMap ℤ ℝ (sigma 0 1) : ℂ)))
  · exact
      ((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ =>
            (algebraMap ℤ ℝ (sigma 1 0) : ℂ))).mul hcurve).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ =>
            (algebraMap ℤ ℝ (sigma 1 1) : ℂ)))
  · exact hden
''' + SECOND,
}

REGION_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
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


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit(
            "usage: qym_patch_gb85_c2_matrix_v2.py "
            f"{'|'.join(sorted(VARIANTS))} QYM.lean"
        )
    variant, filename = sys.argv[1], sys.argv[2]
    path = Path(filename)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("GB85 SHA256 mismatch")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("GB85 Git blob mismatch")

    before_text = before.decode("utf-8")
    before_audit = audit(before_text)
    matches = list(REGION_RE.finditer(before_text))
    if len(matches) != 1:
        raise SystemExit(f"expected one C2 region, found {len(matches)}")
    m = matches[0]
    after_text = (
        before_text[:m.start()]
        + VARIANTS[variant].rstrip()
        + "\n\n"
        + before_text[m.end():]
    )
    after_audit = audit(after_text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(after_text, encoding="utf-8")
    after = path.read_bytes()

    marker = "/-- Every actual smooth trace is Lipschitz"
    marker_index = after_text.find(marker)
    if marker_index < 0:
        raise SystemExit("post-C2 marker missing")
    result = {
        "schema": "qym-gb85-c2-matrix-v2",
        "variant": variant,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": after_text.count("\n", 0, marker_index) + 1,
        "forbidden": after_audit,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
