#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

VARIANTS = {"direct", "structural"}

C7 = r'''theorem actualFixedPhaseCuspBoundaryTransition_contDiff
    (n : ℤ) (kappa : GammaTwoCusp) (Y : ℝ) :
    ContDiff ℝ ∞
      (QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspBoundaryTransition n kappa Y) := by
  have hcurve : ContDiff ℝ ∞
      (fun x : ℝ =>
        ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) :=
    QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspHorocyclePoint_coe_contDiff kappa Y
  have hetaComplex : ContDiffOn ℂ ∞ ModularForm.eta UpperHalfPlane.upperHalfPlaneSet := by
    apply DifferentiableOn.contDiffOn
    · intro z hz
      exact
        (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
    · exact UpperHalfPlane.isOpen_upperHalfPlaneSet
  have heta : ContDiff ℝ ∞
      (fun x : ℝ =>
        ModularForm.eta
          ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
    simpa only [Function.comp_def] using
      (hetaComplex.restrict_scalars ℝ).comp_contDiff hcurve
        (fun x => (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x).2)
  have hshift : ContDiff ℝ ∞ (fun x : ℝ => x + 2) :=
    contDiff_id.add contDiff_const
  have hetaShift : ContDiff ℝ ∞
      (fun x : ℝ =>
        ModularForm.eta
          ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint
              kappa Y (x + 2) : ℍ) : ℂ)) := by
    simpa only [Function.comp_def] using heta.comp hshift
  have hinverseEta : ContDiff ℝ ∞
      (fun x : ℝ =>
        (inverseEtaMultiplier GammaTwo).factor
          (QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspDeckTranslation kappa)
          (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x)) := by
    have hfun :
        (fun x : ℝ =>
          (inverseEtaMultiplier GammaTwo).factor
            (QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspDeckTranslation kappa)
            (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x)) =
          (fun x : ℝ =>
            ModularForm.eta
                ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ) /
              ModularForm.eta
                ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (x + 2) : ℍ) : ℂ)) := by
      funext x
      rw [inverseEtaMultiplier_factor]
      exact (congrArg
        (fun z : ℍ =>
          ModularForm.eta
              ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ) /
            ModularForm.eta (z : ℂ))
        (QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspHorocyclePoint_add_two
          kappa Y x)).symm
    rw [hfun]
    fun_prop (disch := exact ModularForm.eta_ne_zero
      (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y (· + 2)).2)
  let gamma : GL (Fin 2) ℝ :=
    ((((QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspDeckTranslation kappa : GammaTwo) :
      SL(2, ℤ))) : GL (Fin 2) ℝ)
  have hden : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom gamma
          ((QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x : ℍ) : ℂ)) := by
    simpa only [UpperHalfPlane.denom] using
      (contDiff_const.mul hcurve).add contDiff_const
  have hdenNe : ∀ x : ℝ,
      UpperHalfPlane.denom gamma
        (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x) ≠ 0 := by
    intro x
    exact UpperHalfPlane.denom_ne_zero gamma
      (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x)
  have hdenPow : ContDiff ℝ ∞
      (fun x : ℝ =>
        UpperHalfPlane.denom gamma
          (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x) ^
            ((2 : ℤ) * n)) := by
    fun_prop (disch := exact hdenNe _)
  change ContDiff ℝ ∞
    (fun x : ℝ =>
      (inverseEtaPaperOrbitMultiplier GammaTwo n).factor
        (QYM.FullCertification.P2ClassicalHhalfTraceExtension.actualFixedPhaseCuspDeckTranslation kappa)
        (QYM.FullCertification.P2ActualFixedPhaseCuspTraceGraphExtension.actualFixedPhaseCuspHorocyclePoint kappa Y x))
  simpa only [inverseEtaPaperOrbitMultiplier_factor, gamma] using
    hinverseEta.mul hdenPow
'''

C8_DIRECT = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im,
    Complex.inv_re, Complex.inv_im]
  ring
'''

C8_STRUCTURAL = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  by_cases hs : s = 0
  · subst s
    simp [hyperbolicRightNormal]
  · have horth :=
      conj_mul_hyperbolicRightNormal_re y (((s : ℝ) : ℂ) * v)
    have hscaled :
        s * (star v *
          hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
      simpa [map_mul, Complex.star_def, Complex.mul_re,
        mul_assoc, mul_comm, mul_left_comm] using horth
    exact (mul_eq_zero.mp hscaled).resolve_left hs
'''

C9 = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (Complex.normSq w : ℂ) := by
    simpa [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := w)).symm
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hstar]
  simp [Complex.mul_im, Complex.normSq_eq_norm_sq]
  field_simp [hn]
  ring
'''

PATTERNS = {
    "c7": re.compile(r"(?ms)^theorem actualFixedPhaseCuspBoundaryTransition_contDiff\b.*?(?=^/-- In particular the actual transition is Lipschitz)"),
    "c8": re.compile(r"(?ms)^theorem conj_mul_hyperbolicRightNormal_realMultiple_re\b.*?(?=^/-- Exact signed-area formula)"),
    "c9": re.compile(r"(?ms)^theorem conj_mul_hyperbolicRightNormal_im\b.*?(?=^/-! ## 2\. The actual geometric normal)"),
}


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def replace_one(text: str, pattern: re.Pattern[str], replacement: str, label: str) -> str:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"{label}: expected one match, found {len(matches)}")
    match = matches[0]
    return text[:match.start()] + replacement + "\n" + text[match.end():]


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_probe_c7_c9_matrix.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant: {variant}")
    path = Path(filename)
    before = path.read_bytes()
    text = before.decode("utf-8")
    text = replace_one(text, PATTERNS["c7"], C7, "c7")
    text = replace_one(text, PATTERNS["c8"], C8_DIRECT if variant == "direct" else C8_STRUCTURAL, "c8")
    text = replace_one(text, PATTERNS["c9"], C9, "c9")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    decoded = after.decode("utf-8")
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", decoded)),
        "admit": len(re.findall(r"\badmit\b", decoded)),
        "native_decide": len(re.findall(r"\bnative_decide\b", decoded)),
        "Lean.ofReduceBool": decoded.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", decoded)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", decoded)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", decoded)),
    }
    if any(forbidden.values()):
        raise SystemExit(f"forbidden token audit failed: {forbidden}")
    print(json.dumps({
        "schema": "qym-c7-c9-matrix-v1",
        "variant": variant,
        "input_sha256": hashlib.sha256(before).hexdigest(),
        "input_blob": git_blob(before),
        "candidate_sha256": hashlib.sha256(after).hexdigest(),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "forbidden": forbidden,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
