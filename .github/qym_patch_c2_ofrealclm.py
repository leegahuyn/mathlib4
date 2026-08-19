#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "830563b33d873354809594d9e9dce962c1253052f8e70bd4d1513226f7598217"

HEADER = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by'''

COMMON_CURVE = r'''
  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I)
    simpa [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.add contDiff_const
'''

VARIANTS = {
    "clm_named_constants": HEADER + r'''
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by
    simp [g]
''' + COMMON_CURVE + r'''
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
''',
    "clm_direct_constants": HEADER + r'''
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by
    simp [g]
''' + COMMON_CURVE + r'''
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.num] using
      ((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (g 0 0 : ℂ))).mul hcurve).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (g 0 1 : ℂ)))
  have hdenDiff : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.denom] using
      ((contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (g 1 0 : ℂ))).mul hcurve).add
        (contDiff_const : ContDiff ℝ ∞
          (fun _ : ℝ => (g 1 1 : ℂ)))
  have hden : ∀ x : ℝ,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) ≠ 0 := by
    intro x
    exact UpperHalfPlane.denom_ne_zero g
      (actualFixedPhaseHorizontalHorocyclePoint Y x)
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simp_rw [UpperHalfPlane.coe_smul_of_det_pos hg, div_eq_mul_inv]
  exact hnum.mul (hdenDiff.inv hden)
''',
    "clm_special_linear": HEADER + r'''
  let sigma : SL(2, ℤ) := gammaTwoCuspScaling kappa
''' + COMMON_CURVE + r'''
  have ha : ContDiff ℝ ∞
      (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 0 0) : ℂ)) :=
    contDiff_const
  have hb : ContDiff ℝ ∞
      (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 0 1) : ℂ)) :=
    contDiff_const
  have hc : ContDiff ℝ ∞
      (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 1 0) : ℂ)) :=
    contDiff_const
  have hd : ContDiff ℝ ∞
      (fun _ : ℝ => (algebraMap ℤ ℝ (sigma 1 1) : ℂ)) :=
    contDiff_const
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
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(sigma • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simp_rw [UpperHalfPlane.coe_specialLinearGroup_apply, div_eq_mul_inv]
  exact hnum.mul (hdenDiff.inv hden)
''',
}

FIRST_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
    r"(?=^/-- Restriction of every actual real-smooth automorphic core section)"
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
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_c2_ofrealclm.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant {variant!r}; expected one of {sorted(VARIANTS)}")

    path = Path(filename)
    before = path.read_bytes()
    input_sha = hashlib.sha256(before).hexdigest()
    if input_sha != BASE_SHA256:
        raise SystemExit(f"unexpected input SHA256: {input_sha}")

    text = before.decode("utf-8")
    before_audit = audit(text)
    matches = list(FIRST_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected exactly one first-producer theorem, found {len(matches)}")
    match = matches[0]
    text = text[:match.start()] + VARIANTS[variant].rstrip() + "\n\n" + text[match.end():]
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")

    after = path.read_bytes()
    decoded = after.decode("utf-8")
    marker = "/-- Restriction of every actual real-smooth automorphic core section"
    marker_index = decoded.find(marker)
    if marker_index < 0:
        raise SystemExit("could not locate post-producer gate marker")
    gate_line = decoded.count("\n", 0, marker_index) + 1

    print(json.dumps({
        "schema": "qym-c2-ofrealclm-v1",
        "variant": variant,
        "input_sha256": input_sha,
        "input_blob": git_blob(before),
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": gate_line,
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
