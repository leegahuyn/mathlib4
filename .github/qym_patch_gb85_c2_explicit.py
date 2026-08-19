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

TRACE_PROOF = r'''

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

HCURVE = r'''
  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa [actualFixedPhaseHorizontalHorocyclePoint,
      horizontalHorocycleAmbientCurve] using
      (contDiff_horizontalHorocycleAmbientCurve
        (actualFixedPhaseCuspHeight Y))
'''

GL_COMMON = r'''
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by
    simp [g]
''' + HCURVE + r'''
  have hc00 : ContDiff ℝ ∞
      (fun _ : ℝ => (g 0 0 : ℂ)) := contDiff_const
  have hc01 : ContDiff ℝ ∞
      (fun _ : ℝ => (g 0 1 : ℂ)) := contDiff_const
  have hc10 : ContDiff ℝ ∞
      (fun _ : ℝ => (g 1 0 : ℂ)) := contDiff_const
  have hc11 : ContDiff ℝ ∞
      (fun _ : ℝ => (g 1 1 : ℂ)) := contDiff_const
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.num] using
      (hc00.mul hcurve).add hc01
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.denom] using
      (hc10.mul hcurve).add hc11
  have hden : ∀ x : ℝ,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) ≠ 0 := by
    intro x
    exact UpperHalfPlane.denom_ne_zero g
      (actualFixedPhaseHorizontalHorocyclePoint Y x)
'''

VARIANTS = {
    "gl_mul_inv": HEADER + GL_COMMON + r'''
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) /
          UpperHalfPlane.denom g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [div_eq_mul_inv] using
      hnum.mul (hdenDiff.inv hden)
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac
''' + TRACE_PROOF,
    "gl_div": HEADER + GL_COMMON + r'''
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
''' + TRACE_PROOF,
    "sl_mul_inv": HEADER + r'''
  let sigma : SL(2, ℤ) := gammaTwoCuspScaling kappa
''' + HCURVE + r'''
  have ha : ContDiff ℝ ∞
      (fun _ : ℝ =>
        (algebraMap ℤ ℝ (sigma 0 0) : ℂ)) := contDiff_const
  have hb : ContDiff ℝ ∞
      (fun _ : ℝ =>
        (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) := contDiff_const
  have hc : ContDiff ℝ ∞
      (fun _ : ℝ =>
        (algebraMap ℤ ℝ (sigma 1 0) : ℂ)) := contDiff_const
  have hd : ContDiff ℝ ∞
      (fun _ : ℝ =>
        (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) := contDiff_const
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) :=
    (ha.mul hcurve).add hb
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) :=
    (hc.mul hcurve).add hd
  have hden : ∀ x : ℝ,
      (algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ) ≠ 0 := by
    intro x
    simpa [UpperHalfPlane.denom, sigma] using
      (UpperHalfPlane.denom_ne_zero
        ((gammaTwoCuspScaling kappa : SL(2, ℤ)) : GL (Fin 2) ℝ)
        (actualFixedPhaseHorizontalHorocyclePoint Y x))
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        ((algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
              (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
            (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) /
          ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
              (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
            (algebraMap ℤ ℝ (sigma 1 1) : ℂ))) := by
    simpa only [div_eq_mul_inv] using
      hnum.mul (hdenDiff.inv hden)
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(sigma • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_specialLinearGroup_apply] using hfrac
''' + TRACE_PROOF,
}

REGION_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
    r"(?=^/-- Every actual smooth trace is Lipschitz)"
)


def git_blob(data: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(data)).encode() + b"\0" + data
    ).hexdigest()


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
    if len(sys.argv) != 3:
        raise SystemExit(
            "usage: qym_patch_gb85_c2_explicit.py VARIANT QYM.lean"
        )
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(
            f"unknown variant {variant!r}; expected one of {sorted(VARIANTS)}"
        )

    path = Path(filename)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256:
        raise SystemExit("GB85 SHA256 mismatch")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("GB85 Git blob mismatch")

    text = before.decode("utf-8")
    before_audit = audit(text)
    replacement = VARIANTS[variant].rstrip() + "\n\n"
    text, count = REGION_RE.subn(replacement, text)
    if count != 1:
        raise SystemExit(f"expected one C2 region, replaced {count}")
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(
            f"forbidden-token delta: {before_audit} -> {after_audit}"
        )
    path.write_text(text, encoding="utf-8")

    after = path.read_bytes()
    marker = "/-- Every actual smooth trace is Lipschitz"
    marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit("post-C2 gate marker missing")

    result = {
        "schema": "qym-gb85-c2-explicit-v1",
        "variant": variant,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": text.count("\n", 0, marker_index) + 1,
        "forbidden": after_audit,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
