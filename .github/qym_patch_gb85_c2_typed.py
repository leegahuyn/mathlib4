#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "f4c9b27a297be772cde7183526378ad42ae826053f69cf3ce521670da4f06210"
BASE_BLOB = "bd28d0436230a8f0bcb01806dac01787542256b8"
VARIANTS = {"change_div", "change_mul_inv", "seeded_fun_prop", "numden_div"}

SECOND = r'''/-- Restriction of every actual real-smooth automorphic core section to a
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
  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) :=
    actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y
  exact hu.comp_contDiff hcurve
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
'''

HEADER = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  let sigma : SL(2, ℤ) := gammaTwoCuspScaling kappa
  have hx : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff :
        ContDiff ℝ ∞ (fun x : ℝ => Complex.ofRealCLM x))
  have hc : ContDiff ℝ ∞
      (fun _ : ℝ =>
        (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) :=
    contDiff_const
  have hz : ContDiff ℝ ∞
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) :=
    hx.add hc
  have hden : ∀ x : ℝ,
      ((algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) +
        (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) ≠ 0 := by
    intro x
    simpa [UpperHalfPlane.denom, sigma] using
      (UpperHalfPlane.denom_ne_zero
        (sigma : GL (Fin 2) ℝ)
        (actualFixedPhaseHorizontalHorocyclePoint Y x))
  simp only [actualFixedPhaseCuspHorocyclePoint,
    actualFixedPhaseHorizontalHorocyclePoint,
    UpperHalfPlane.coe_specialLinearGroup_apply]
'''

CHANGE_DIV = HEADER + r'''  apply ContDiff.div
  · exact (contDiff_const.mul hz).add contDiff_const
  · exact (contDiff_const.mul hz).add contDiff_const
  · simpa only [actualFixedPhaseHorizontalHorocyclePoint] using hden
''' + SECOND

CHANGE_MUL_INV = HEADER + r'''  rw [div_eq_mul_inv]
  exact ((contDiff_const.mul hz).add contDiff_const).mul
    (((contDiff_const.mul hz).add contDiff_const).inv
      (by simpa only [actualFixedPhaseHorizontalHorocyclePoint] using hden))
''' + SECOND

SEEDED_FUN_PROP = HEADER + r'''  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 0 0) : ℂ) *
            ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
          (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) :=
    (contDiff_const.mul hz).add contDiff_const
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        (algebraMap ℤ ℝ (sigma 1 0) : ℂ) *
            ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
          (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) :=
    (contDiff_const.mul hz).add contDiff_const
  exact hnum.div hdenDiff
    (by simpa only [actualFixedPhaseHorizontalHorocyclePoint] using hden)
''' + SECOND

NUMDEN_DIV = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by
    simp [g]
  have hx : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff :
        ContDiff ℝ ∞ (fun x : ℝ => Complex.ofRealCLM x))
  have hz : ContDiff ℝ ∞
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) :=
    hx.add contDiff_const
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.num,
      actualFixedPhaseHorizontalHorocyclePoint] using
      (contDiff_const.mul hz).add contDiff_const
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.denom,
      actualFixedPhaseHorizontalHorocyclePoint] using
      (contDiff_const.mul hz).add contDiff_const
  have hden : ∀ x : ℝ,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x) ≠ 0 := by
    intro x
    exact UpperHalfPlane.denom_ne_zero g
      (actualFixedPhaseHorizontalHorocyclePoint Y x)
  have hfrac := hnum.div hdenDiff hden
  simp only [actualFixedPhaseCuspHorocyclePoint]
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac
''' + SECOND

PROOFS = {
    "change_div": CHANGE_DIV,
    "change_mul_inv": CHANGE_MUL_INV,
    "seeded_fun_prop": SEEDED_FUN_PROP,
    "numden_div": NUMDEN_DIV,
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
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit("usage: qym_patch_gb85_c2_typed.py VARIANT QYM.lean")
    variant, path = sys.argv[1], Path(sys.argv[2])
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASE_SHA256 or git_blob(before) != BASE_BLOB:
        raise SystemExit("exact GB85 authority mismatch")
    text = before.decode("utf-8")
    before_audit = audit(text)
    matches = list(REGION_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected one C2 region, found {len(matches)}")
    match = matches[0]
    text = text[:match.start()] + PROOFS[variant].rstrip() + "\n\n" + text[match.end():]
    after_audit = audit(text)
    if after_audit != before_audit or any(after_audit.values()):
        raise SystemExit(f"forbidden audit changed: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    marker = "/-- Every actual smooth trace is Lipschitz"
    marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit("C2 gate marker missing")
    print(json.dumps({
        "schema": "qym-gb85-c2-typed-v1",
        "variant": variant,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": text.count("\n", 0, marker_index) + 1,
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
