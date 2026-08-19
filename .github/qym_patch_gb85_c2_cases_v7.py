#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASELINE_SHA256 = "f4c9b27a297be772bf863001175d540fd024e22ce0bec06af75f47ef48c23bba1"
BASELINE_BLOB = "bd28d043181c53d405eed7659d7018fa2298a33d"

HOROCYCLE_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff\b.*?"
    r"(?=^/-- Restriction of every actual real-smooth automorphic core section)"
)
TRACE_RE = re.compile(
    r"(?ms)^theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff\b.*?"
    r"(?=^/-- Every actual smooth trace is Lipschitz)"
)

CASES_EXPLICIT = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseHorizontalHorocyclePoint Y x : ℍ) : ℂ)) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x : ℝ =>
        (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I)
    simpa [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.add contDiff_const
  have hneg_ne : ∀ x : ℝ,
      -((actualFixedPhaseHorizontalHorocyclePoint Y x : ℍ) : ℂ) ≠ 0 := by
    intro x hx
    have him := congrArg Complex.im hx
    simp [actualFixedPhaseHorizontalHorocyclePoint] at him
    linarith [actualFixedPhaseCuspHeight_pos Y]
  have hinv : ContDiff ℝ ∞
      (fun x : ℝ =>
        (-((actualFixedPhaseHorizontalHorocyclePoint Y x : ℍ) : ℂ))⁻¹) := by
    exact hcurve.neg.inv hneg_ne
  cases kappa with
  | atInfinity =>
      simpa [actualFixedPhaseCuspHorocyclePoint,
        gammaTwoCuspScaling_atInfinity] using hcurve
  | zero =>
      simpa [actualFixedPhaseCuspHorocyclePoint,
        gammaTwoCuspScaling_zero,
        UpperHalfPlane.modular_S_smul] using hinv
  | one =>
      have hone : ContDiff ℝ ∞
          (fun x : ℝ =>
            (1 : ℂ) +
              (-((actualFixedPhaseHorizontalHorocyclePoint Y x : ℍ) : ℂ))⁻¹) :=
        contDiff_const.add hinv
      simpa [actualFixedPhaseCuspHorocyclePoint,
        gammaTwoCuspScaling_one, mul_smul,
        UpperHalfPlane.modular_S_smul,
        UpperHalfPlane.modular_T_smul,
        UpperHalfPlane.coe_vadd] using hone
'''

CASES_CHANGE = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
    (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ =>
        ((actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
  cases kappa with
  | atInfinity =>
      change ContDiff ℝ ∞
        (fun x : ℝ =>
          ((actualFixedPhaseHorizontalHorocyclePoint Y x : ℍ) : ℂ))
      change ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun x : ℝ =>
          (x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I)
      simpa [Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.contDiff.add contDiff_const
  | zero =>
      simp only [actualFixedPhaseCuspHorocyclePoint,
        gammaTwoCuspScaling_zero,
        UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
      apply ContDiff.inv
      · change ContDiff ℝ ∞
          (fun x : ℝ =>
            -((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I))
        fun_prop
      · intro x hx
        have him := congrArg Complex.im hx
        simp [actualFixedPhaseHorizontalHorocyclePoint] at him
        linarith [actualFixedPhaseCuspHeight_pos Y]
  | one =>
      simp only [actualFixedPhaseCuspHorocyclePoint,
        gammaTwoCuspScaling_one, mul_smul,
        UpperHalfPlane.modular_S_smul,
        UpperHalfPlane.modular_T_smul,
        UpperHalfPlane.coe_mk, UpperHalfPlane.coe_vadd]
      apply ContDiff.add
      · fun_prop
      · apply ContDiff.inv
        · change ContDiff ℝ ∞
            (fun x : ℝ =>
              -((x : ℂ) + (actualFixedPhaseCuspHeight Y : ℂ) * Complex.I))
          fun_prop
        · intro x hx
          have him := congrArg Complex.im hx
          simp [actualFixedPhaseHorizontalHorocyclePoint] at him
          linarith [actualFixedPhaseCuspHeight_pos Y]
'''

INTRINSIC_DETPOS = r'''theorem actualFixedPhaseCuspHorocyclePoint_coe_contDiff
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
  have hg : 0 < g.val.det := by
    simpa [g] using
      Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseIntrinsicAdjointCutoff.integralMoebius_det_pos
        (gammaTwoCuspScaling kappa)
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

TRACE_PROOF = r'''theorem actualFixedPhaseNamedCuspTraceRepresentative_contDiff
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

VARIANTS = {
    "cases_explicit": CASES_EXPLICIT,
    "cases_change": CASES_CHANGE,
    "intrinsic_detpos": INTRINSIC_DETPOS,
}


def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def forbidden(text: str) -> dict[str, int]:
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
    m = matches[0]
    return text[:m.start()] + replacement.rstrip() + "\n\n" + text[m.end():]


def main() -> None:
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit(
            f"usage: {sys.argv[0]} <{'|'.join(VARIANTS)}> QYM.lean"
        )
    variant, filename = sys.argv[1], sys.argv[2]
    path = Path(filename)
    before = path.read_bytes()
    if hashlib.sha256(before).hexdigest() != BASELINE_SHA256:
        raise SystemExit("baseline SHA256 mismatch")
    if git_blob(before) != BASELINE_BLOB:
        raise SystemExit("baseline Git blob mismatch")

    text = before.decode("utf-8")
    audit_before = forbidden(text)
    text = replace_one(
        HOROCYCLE_RE, VARIANTS[variant], text,
        "actualFixedPhaseCuspHorocyclePoint_coe_contDiff",
    )
    text = replace_one(
        TRACE_RE, TRACE_PROOF, text,
        "actualFixedPhaseNamedCuspTraceRepresentative_contDiff",
    )
    audit_after = forbidden(text)
    if audit_after != audit_before:
        raise SystemExit(f"forbidden-token delta: {audit_before} -> {audit_after}")

    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    marker = "/-- Every actual smooth trace is Lipschitz"
    marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit("post-C2 marker not found")
    gate_line = text.count("\n", 0, marker_index) + 1

    print(json.dumps({
        "schema": "qym-gb85-c2-cases-v7",
        "variant": variant,
        "input_sha256": BASELINE_SHA256,
        "input_blob": BASELINE_BLOB,
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": gate_line,
        "forbidden": audit_after,
        "targets": [
            "actualFixedPhaseCuspHorocyclePoint_coe_contDiff",
            "actualFixedPhaseNamedCuspTraceRepresentative_contDiff",
        ],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
