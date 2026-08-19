#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASELINE_SHA256 = "313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e"
BASELINE_BLOB = "ff49510790dd7ca136bf34c3ec7150617ee1c241"

OLD_HOROCYCLE = '''/-- The complex coordinate of every named-cusp horocycle parametrization is
real `C-infinity`.  This is a direct rational-map calculation; the denominator
cannot vanish on the upper half-plane. -/
theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  let sigma : SL(2, ℤ) := gammaTwoCuspScaling kappa
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
  rw [div_eq_mul_inv]
  apply ContDiff.mul
  · fun_prop
  · apply ContDiff.inv
    · fun_prop
    · exact hden
'''

NEW_HOROCYCLE = '''/-- The complex coordinate of every named-cusp horocycle parametrization is
real `C-infinity`.  We use the intrinsic holomorphic Mobius action and then
restrict scalars to `R`, avoiding noncanonical complex normed instances. -/
theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (((gammaTwoCuspScaling kappa : GL (Fin 2) ℝ) •
        actualFixedPhaseHorizontalHorocyclePoint Y x : ℍ) : ℂ))
  let g : GL (Fin 2) ℝ :=
    (gammaTwoCuspScaling kappa : GL (Fin 2) ℝ)
  have hdet : g.val.det = 1 := by
    simpa [g] using congrArg (fun u : ℝˣ => (u : ℝ))
      (Matrix.SpecialLinearGroup.coeToGL_det
        (gammaTwoCuspScaling kappa : SL(2, ℝ)))
  have hg : 0 < g.val.det := by
    rw [hdet]
    norm_num
  have hmobDiff : DifferentiableOn ℂ
      (fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ))
      UpperHalfPlane.upperHalfPlaneSet := by
    intro w hw
    exact
      (UpperHalfPlane.hasStrictDerivAt_smul (g := g) hg
        (⟨w, hw⟩ : ℍ)).differentiableAt.differentiableWithinAt
  have hmob : ContDiffOn ℝ ∞
      (fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : ℍ) : ℂ))
      UpperHalfPlane.upperHalfPlaneSet :=
    (hmobDiff.analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet).restrictScalars.contDiffOn_of_completeSpace
  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseHorizontalHorocyclePoint Y x : ℍ) : ℂ)) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I)
    simpa [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.add contDiff_const
  have hcomp := hmob.comp_contDiff hcurve
    (fun x => (actualFixedPhaseHorizontalHorocyclePoint Y x).2)
  simpa [g] using hcomp
'''

OLD_TRACE = '''  have hcurve := actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y
  have hcomp := hu.comp_contDiff hcurve
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
  change ContDiff ℝ ∞
    (upperLift ((u : SmoothQuotientCompactFunction) : ℍ → ℂ) ∘
      fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ))
  exact hcomp
'''

NEW_TRACE = '''  have hcurve := actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y
  have hcomp := hu.comp_contDiff hcurve
    (fun x => (actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
  simpa only [actualFixedPhaseNamedCuspTraceRepresentative,
    upperLift_apply] using hcomp
'''


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def counts(text: str) -> dict[str, int]:
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
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} QYM.lean")
    path = Path(sys.argv[1])
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASELINE_SHA256:
        raise SystemExit("baseline SHA256 mismatch")
    if git_blob(before) != BASELINE_BLOB:
        raise SystemExit("baseline Git blob mismatch")
    text = before.decode("utf-8")
    before_forbidden = counts(text)
    for label, old, new in [
        ("horocycle", OLD_HOROCYCLE, NEW_HOROCYCLE),
        ("trace", OLD_TRACE, NEW_TRACE),
    ]:
        count = text.count(old)
        if count != 1:
            raise SystemExit(f"{label} replacement count = {count}, expected 1")
        text = text.replace(old, new, 1)
    after_forbidden = counts(text)
    if after_forbidden != before_forbidden:
        raise SystemExit(f"forbidden-token delta: {before_forbidden} -> {after_forbidden}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    print(json.dumps({
        "schema": "qym-c02-structural-v1",
        "variant": "intrinsic_mobius",
        "input_sha256": BASELINE_SHA256,
        "input_blob": BASELINE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "fixed_producers_targeted": [
            "actualFixedPhaseCuspHorocyclePoint_coe_contDiff",
            "actualFixedPhaseNamedCuspTraceRepresentative_contDiff"
        ],
        "forbidden_before": before_forbidden,
        "forbidden_after": after_forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
