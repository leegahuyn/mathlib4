#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

HEADER = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by'''

COMMON = r'''
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hg : 0 < g.det.val := by
    simp [g]
  have hx : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
    exact Complex.ofRealCLM.contDiff
  have hz : ContDiff ℝ ∞
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) := by
    exact hx.add contDiff_const
  have hc00 : ContDiff ℝ ∞
      (fun _ : ℝ => ((g 0 0 : ℝ) : ℂ)) := contDiff_const
  have hc01 : ContDiff ℝ ∞
      (fun _ : ℝ => ((g 0 1 : ℝ) : ℂ)) := contDiff_const
  have hc10 : ContDiff ℝ ∞
      (fun _ : ℝ => ((g 1 0 : ℝ) : ℂ)) := contDiff_const
  have hc11 : ContDiff ℝ ∞
      (fun _ : ℝ => ((g 1 1 : ℝ) : ℂ)) := contDiff_const
  have hnumExpanded : ContDiff ℝ ∞
      (fun x : ℝ =>
        ((g 0 0 : ℝ) : ℂ) *
            ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
          ((g 0 1 : ℝ) : ℂ)) := by
    exact (hc00.mul hz).add hc01
  have hdenExpanded : ContDiff ℝ ∞
      (fun x : ℝ =>
        ((g 1 0 : ℝ) : ℂ) *
            ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
          ((g 1 1 : ℝ) : ℂ)) := by
    exact (hc10.mul hz).add hc11
  have hden_ne_expanded : ∀ x : ℝ,
      ((g 1 0 : ℝ) : ℂ) *
            ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
          ((g 1 1 : ℝ) : ℂ) ≠ 0 := by
    intro x
    simpa only [UpperHalfPlane.denom,
      actualFixedPhaseHorizontalHorocyclePoint] using
      (UpperHalfPlane.denom_ne_zero g
        (actualFixedPhaseHorizontalHorocyclePoint Y x))
'''

CLM_UPPER_DIV = HEADER + COMMON + r'''
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.num,
      actualFixedPhaseHorizontalHorocyclePoint] using hnumExpanded
  have hden : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.denom,
      actualFixedPhaseHorizontalHorocyclePoint] using hdenExpanded
  have hden_ne : ∀ x : ℝ,
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
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) :=
    hnum.div hden hden_ne
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg] using hfrac
'''

CLM_UPPER_INV = HEADER + COMMON + r'''
  have hnum : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.num,
      actualFixedPhaseHorizontalHorocyclePoint] using hnumExpanded
  have hden : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom g
          (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ)) := by
    simpa only [UpperHalfPlane.denom,
      actualFixedPhaseHorizontalHorocyclePoint] using hdenExpanded
  have hden_ne : ∀ x : ℝ,
      UpperHalfPlane.denom g
        (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) ≠ 0 := by
    intro x
    exact UpperHalfPlane.denom_ne_zero g
      (actualFixedPhaseHorizontalHorocyclePoint Y x)
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.num g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ) *
          (UpperHalfPlane.denom g
            (actualFixedPhaseHorizontalHorocyclePoint Y x : ℂ))⁻¹) :=
    hnum.mul (hden.inv hden_ne)
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg,
    div_eq_mul_inv] using hfrac
'''

CLM_EXPANDED_DIV = HEADER + COMMON + r'''
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        (((g 0 0 : ℝ) : ℂ) *
              ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
            ((g 0 1 : ℝ) : ℂ)) /
          (((g 1 0 : ℝ) : ℂ) *
              ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
            ((g 1 1 : ℝ) : ℂ))) :=
    hnumExpanded.div hdenExpanded hden_ne_expanded
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg,
    UpperHalfPlane.num, UpperHalfPlane.denom,
    actualFixedPhaseHorizontalHorocyclePoint] using hfrac
'''

CLM_EXPANDED_INV = HEADER + COMMON + r'''
  have hfrac : ContDiff ℝ ∞
      (fun x : ℝ =>
        (((g 0 0 : ℝ) : ℂ) *
              ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
            ((g 0 1 : ℝ) : ℂ)) *
          ((((g 1 0 : ℝ) : ℂ) *
              ((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I) +
            ((g 1 1 : ℝ) : ℂ)))⁻¹) :=
    hnumExpanded.mul (hdenExpanded.inv hden_ne_expanded)
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simpa only [UpperHalfPlane.coe_smul_of_det_pos hg,
    UpperHalfPlane.num, UpperHalfPlane.denom,
    actualFixedPhaseHorizontalHorocyclePoint, div_eq_mul_inv] using hfrac
'''

CLM_CHANGE_RW = HEADER + COMMON + r'''
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (↑(g • actualFixedPhaseHorizontalHorocyclePoint Y x) : ℂ))
  simp_rw [UpperHalfPlane.coe_smul_of_det_pos hg]
  apply ContDiff.div
  · simpa only [UpperHalfPlane.num,
      actualFixedPhaseHorizontalHorocyclePoint] using hnumExpanded
  · simpa only [UpperHalfPlane.denom,
      actualFixedPhaseHorizontalHorocyclePoint] using hdenExpanded
  · intro x
    exact UpperHalfPlane.denom_ne_zero g
      (actualFixedPhaseHorizontalHorocyclePoint Y x)
'''

VARIANTS = {
    "clm_upper_div": CLM_UPPER_DIV,
    "clm_upper_inv": CLM_UPPER_INV,
    "clm_expanded_div": CLM_EXPANDED_DIV,
    "clm_expanded_inv": CLM_EXPANDED_INV,
    "clm_change_rw": CLM_CHANGE_RW,
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
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit(
            "usage: qym_patch_gb85_c2_explicit_clm.py VARIANT QYM.lean"
        )
    variant = sys.argv[1]
    path = Path(sys.argv[2])
    before = path.read_bytes()
    text = before.decode("utf-8")
    before_audit = audit(text)
    matches = list(FIRST_RE.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected one C2 producer theorem, found {len(matches)}")
    m = matches[0]
    text = text[:m.start()] + VARIANTS[variant].rstrip() + "\n\n" + text[m.end():]
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    marker = "/-- Restriction of every actual real-smooth automorphic core section"
    marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit("post-C2 gate marker missing")
    print(json.dumps({
        "schema": "qym-gb85-c2-explicit-clm-v1",
        "variant": variant,
        "input_sha256": hashlib.sha256(before).hexdigest(),
        "input_blob": git_blob(before),
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": text.count("\n", 0, marker_index) + 1,
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
