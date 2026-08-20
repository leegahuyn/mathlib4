#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASE_SHA256 = "ea7c26fd104104e852a6c678017b1fb0c76abb062edd758228c4bbe506dbe8d1"
BASE_BLOB = "43aee9530d6c665fbc5e082b3a5b3ef3367f069b"

PREFIX = r'''theorem baseEdgeCoordinate_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) {t : ℝ}
    (ht : t ∈ QYM.FullCertification.P2NormalGreenExtension.regularEdgeParameterSet e) :
    HasDerivAt (baseEdgeCoordinate e.2)
      (baseEdgeVelocity e.2 t) t := by
  letI : AddCommGroup ℂ := Complex.addCommGroup
  rcases e with ⟨q, k⟩
  cases k with
  | circularArc =>
      have hx :
          HasDerivAt (fun s : ℝ => ((s / 2 : ℝ) : ℂ))
            (((1 : ℝ) / 2 : ℝ) : ℂ) t :=
        ((hasDerivAt_id t).div_const 2).ofReal_comp
      have hy :
          HasDerivAt
            (fun s : ℝ =>
              ((Real.sqrt (1 - (s / 2) ^ 2) : ℝ) : ℂ))
            ((-t / (4 * Real.sqrt (1 - (t / 2) ^ 2)) : ℝ) : ℂ) t :=
        (hasDerivAt_circularHeight ht).ofReal_comp
      have h0 := hx.add (hy.mul_const Complex.I)
'''

CIRCULAR_RW = r'''      have hfun :
          ((fun s : ℝ => ((s / 2 : ℝ) : ℂ)) +
            fun s : ℝ =>
              ((Real.sqrt (1 - (s / 2) ^ 2) : ℝ) : ℂ) * Complex.I) =
            (fun s : ℝ =>
              Complex.mk (s / 2) (Real.sqrt (1 - (s / 2) ^ 2))) := by
        funext s
        apply Complex.ext <;> simp
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk (s / 2) (Real.sqrt (1 - (s / 2) ^ 2)))
        (Complex.mk ((1 : ℝ) / 2)
          (-t / (4 * Real.sqrt (1 - (t / 2) ^ 2)))) t
      rw [← hfun]
      simpa [Complex.mk_eq_add_mul_I] using h0
'''

CIRCULAR_CONGR = r'''      have h1 := h0.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun s => by
          change
            ((s / 2 : ℝ) : ℂ) +
                ((Real.sqrt (1 - (s / 2) ^ 2) : ℝ) : ℂ) * Complex.I =
              Complex.mk (s / 2) (Real.sqrt (1 - (s / 2) ^ 2))
          apply Complex.ext <;> simp))
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk (s / 2) (Real.sqrt (1 - (s / 2) ^ 2)))
        (Complex.mk ((1 : ℝ) / 2)
          (-t / (4 * Real.sqrt (1 - (t / 2) ^ 2)))) t
      simpa [Complex.mk_eq_add_mul_I] using h1
'''

VERTICALS = r'''  | leftVerticalSegment =>
      let c : ℂ :=
        Complex.mk (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2)
      have hs : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t :=
        (hasDerivAt_id t).ofReal_comp
      have h0 := (hasDerivAt_const t c).add (hs.mul_const Complex.I)
      have hfun :
          ((fun _ : ℝ => c) + fun s : ℝ => (s : ℂ) * Complex.I) =
            (fun s : ℝ =>
              Complex.mk (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2 + s)) := by
        funext s
        apply Complex.ext <;> simp [c]
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2 + s))
        Complex.I t
      rw [← hfun]
      simpa using h0
  | rightVerticalSegment =>
      let c : ℂ :=
        Complex.mk ((1 : ℝ) / 2) (Real.sqrt 3 / 2)
      have hs : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t :=
        (hasDerivAt_id t).ofReal_comp
      have h0 := (hasDerivAt_const t c).add (hs.mul_const Complex.I)
      have hfun :
          ((fun _ : ℝ => c) + fun s : ℝ => (s : ℂ) * Complex.I) =
            (fun s : ℝ =>
              Complex.mk ((1 : ℝ) / 2) (Real.sqrt 3 / 2 + s)) := by
        funext s
        apply Complex.ext <;> simp [c]
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk ((1 : ℝ) / 2) (Real.sqrt 3 / 2 + s))
        Complex.I t
      rw [← hfun]
      simpa using h0
'''

DET_COE = r'''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  letI : AddCommGroup ℂ := Complex.addCommGroup
  have hdet : (selectedRepresentativeRealMatrix q).val.det = 1 := by
    simpa [selectedRepresentativeRealMatrix] using
      (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q :
        SL(2, ℝ)).det_coe
  have hraw :=
    UpperHalfPlane.hasStrictDerivAt_smul
      (g := selectedRepresentativeRealMatrix q) (by
        rw [hdet]
        norm_num) z
  rw [hdet] at hraw
  simpa [selectedRepresentativeChart, selectedRepresentativeCoordinate,
    selectedRepresentativeDenom, selectedRepresentativeRealMatrix] using hraw
'''

DET_GL = r'''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  letI : AddCommGroup ℂ := Complex.addCommGroup
  let gR : SL(2, ℝ) :=
    (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q :
      SL(2, ℝ))
  have hdet : (selectedRepresentativeRealMatrix q).val.det = 1 := by
    have hunit := Matrix.SpecialLinearGroup.coeToGL_det gR
    have hval := congrArg (fun u : ℝˣ => (u : ℝ)) hunit
    simpa [gR, selectedRepresentativeRealMatrix,
      Matrix.GeneralLinearGroup.val_det_apply] using hval
  have hraw :=
    UpperHalfPlane.hasStrictDerivAt_smul
      (g := selectedRepresentativeRealMatrix q) (by
        rw [hdet]
        norm_num) z
  rw [hdet] at hraw
  simpa [selectedRepresentativeChart, selectedRepresentativeCoordinate,
    selectedRepresentativeDenom, selectedRepresentativeRealMatrix] using hraw
'''

DET_CHANGE = r'''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  letI : AddCommGroup ℂ := Complex.addCommGroup
  let gR : SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
      (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q)
  have hg : selectedRepresentativeRealMatrix q = (gR : GL (Fin 2) ℝ) := by
    rfl
  have hdet : (selectedRepresentativeRealMatrix q).val.det = 1 := by
    rw [hg]
    exact gR.det_coe
  have hraw :=
    UpperHalfPlane.hasStrictDerivAt_smul
      (g := selectedRepresentativeRealMatrix q) (by
        rw [hdet]
        norm_num) z
  rw [hdet] at hraw
  simpa [selectedRepresentativeChart, selectedRepresentativeCoordinate,
    selectedRepresentativeDenom, selectedRepresentativeRealMatrix] using hraw
'''

VARIANTS = {
    "rw_det_coe": PREFIX + CIRCULAR_RW + VERTICALS + "\n" + DET_COE,
    "congr_det_gl": PREFIX + CIRCULAR_CONGR + VERTICALS + "\n" + DET_GL,
    "rw_det_change": PREFIX + CIRCULAR_RW + VERTICALS + "\n" + DET_CHANGE,
}

BASE_RE = re.compile(
    r"(?ms)^theorem baseEdgeCoordinate_hasDerivAt\b.*?"
    r"(?=^/-! ## 4\. Transport through the selected coset representative)"
)
DET_RE = re.compile(
    r"(?ms)^theorem selectedRepresentativeChart_hasStrictDerivAt\b.*?"
    r"(?=^/-- Fully explicit complex coordinate of an actual selected polygon edge)"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


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
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }


def replace_one(pattern: re.Pattern[str], replacement: str, text: str, label: str) -> str:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise SystemExit(f"expected exactly one {label}, found {len(matches)}")
    m = matches[0]
    return text[:m.start()] + replacement.rstrip() + "\n\n" + text[m.end():]


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_patch_gb83_v10_normalize4.py VARIANT QYM.lean")
    variant, filename = sys.argv[1], sys.argv[2]
    if variant not in VARIANTS:
        raise SystemExit(f"unknown variant {variant!r}; expected {sorted(VARIANTS)}")
    path = Path(filename)
    before = path.read_bytes()
    if sha256(before) != BASE_SHA256:
        raise SystemExit("unexpected GB83 input SHA256")
    if git_blob(before) != BASE_BLOB:
        raise SystemExit("unexpected GB83 input Git blob")
    text = before.decode("utf-8")
    before_audit = audit(text)
    replacement = VARIANTS[variant]
    split = replacement.index("theorem selectedRepresentativeChart_hasStrictDerivAt")
    base_replacement = replacement[:split].rstrip()
    det_replacement = replacement[split:].rstrip()
    text = replace_one(BASE_RE, base_replacement, text, "base-edge derivative theorem")
    text = replace_one(DET_RE, det_replacement, text, "selected-representative derivative theorem")
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(text, encoding="utf-8")
    after = path.read_bytes()
    marker = "theorem edgeParameterTransport_hasDerivAt"
    marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit("could not locate V11 gate marker")
    gate_line = text.count("\n", 0, marker_index) + 1
    print(json.dumps({
        "schema": "qym-gb83-v10-normalize4-patch-v1",
        "variant": variant,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": sha256(after),
        "candidate_blob": git_blob(after),
        "bytes": len(after),
        "lf": after.count(b"\n"),
        "gate_line": gate_line,
        "forbidden": after_audit,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
