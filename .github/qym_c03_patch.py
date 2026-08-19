#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

BASELINE_SHA256 = "313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e"
BASELINE_BLOB = "ff49510790dd7ca136bf34c3ec7150617ee1c241"

REPLACEMENTS = [
("circular", '''      simpa [Complex.mk_eq_add_mul_I] using
        hx.add (hy.mul_const Complex.I)
''', '''      simpa only [Complex.mk_eq_add_mul_I] using!
        hx.add (hy.mul_const Complex.I)
'''),
("left_vertical", '''  | leftVerticalSegment =>
      have h :=
        ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
            ((-((1 : ℝ) / 2) : ℂ) +
              ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I))
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa [baseEdgeCoordinate, baseEdgeVelocity,
        Complex.mk_eq_add_mul_I, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using h
''', '''  | leftVerticalSegment =>
      have hy : HasDerivAt
          (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have h := (hy.ofReal_comp.mul_const Complex.I).const_add
        (-((1 : ℝ) / 2) : ℂ)
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa only [Complex.mk_eq_add_mul_I, one_mul] using! h
'''),
("right_vertical", '''  | rightVerticalSegment =>
      have h :=
        ((((hasDerivAt_id (t : ℂ)).const_mul Complex.I).comp_ofReal).const_add
            ((((1 : ℝ) / 2 : ℝ) : ℂ) +
              ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I))
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk ((1 : ℝ) / 2) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa [baseEdgeCoordinate, baseEdgeVelocity,
        Complex.mk_eq_add_mul_I, add_mul,
        mul_comm, mul_left_comm, mul_assoc] using h
''', '''  | rightVerticalSegment =>
      have hy : HasDerivAt
          (fun s : ℝ => Real.sqrt 3 / 2 + s) 1 t :=
        (hasDerivAt_const t (Real.sqrt 3 / 2)).add (hasDerivAt_id t)
      have h := (hy.ofReal_comp.mul_const Complex.I).const_add
        (((1 : ℝ) / 2 : ℝ) : ℂ)
      change HasDerivAt
        (fun s : ℝ =>
          Complex.mk ((1 : ℝ) / 2) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa only [Complex.mk_eq_add_mul_I, one_mul] using! h
'''),
("selected_representative", '''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  simpa [selectedRepresentativeChart, selectedRepresentativeCoordinate,
    selectedRepresentativeDenom, selectedRepresentativeRealMatrix,
    one_div] using
      (UpperHalfPlane.hasStrictDerivAt_smul
        (g := selectedRepresentativeRealMatrix q) (by
          change 0 <
            (((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q :
              SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det
          exact
            Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseIntrinsicAdjointCutoff.integralMoebius_det_pos
              (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q)) z)
''', '''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  have hdet : (selectedRepresentativeRealMatrix q).val.det = 1 := by
    simpa [selectedRepresentativeRealMatrix] using
      congrArg (fun u : ℝˣ => (u : ℝ))
        (Matrix.SpecialLinearGroup.coeToGL_det
          ((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q :
            SL(2, ℤ)) : SL(2, ℝ)))
  have hpos : 0 < (selectedRepresentativeRealMatrix q).val.det := by
    rw [hdet]
    norm_num
  have hraw := UpperHalfPlane.hasStrictDerivAt_smul
    (g := selectedRepresentativeRealMatrix q) hpos z
  rw [hdet] at hraw
  simpa [selectedRepresentativeChart, selectedRepresentativeCoordinate,
    selectedRepresentativeDenom, selectedRepresentativeRealMatrix,
    one_div] using hraw
'''),
("parameter_transport", '''  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
''', '''  simpa only [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using!
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''),
]


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
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} QYM.lean")
    path=Path(sys.argv[1]); before=path.read_bytes()
    if hashlib.sha256(before).hexdigest()!=BASELINE_SHA256 or git_blob(before)!=BASELINE_BLOB:
        raise SystemExit("baseline authority mismatch")
    text=before.decode('utf-8'); before_audit=audit(text)
    for label,old,new in REPLACEMENTS:
        count=text.count(old)
        if count!=1:
            raise SystemExit(f"{label} replacement count={count}, expected 1")
        text=text.replace(old,new,1)
    after_audit=audit(text)
    if after_audit!=before_audit:
        raise SystemExit(f"forbidden-token delta: {before_audit} -> {after_audit}")
    path.write_text(text,encoding='utf-8'); after=path.read_bytes()
    print(json.dumps({
      'schema':'qym-c03-edge-derivatives-v1','variant':'using_bang_explicit_constants',
      'input_sha256':BASELINE_SHA256,'input_blob':BASELINE_BLOB,
      'candidate_sha256':hashlib.sha256(after).hexdigest(),'candidate_blob':git_blob(after),
      'bytes':len(after),'lf':after.count(b'\n'),
      'fixed_producers_targeted':['baseEdgeCoordinate_hasDerivAt','selectedRepresentativeChart_hasStrictDerivAt','edgeParameterTransport_hasDerivAt'],
      'forbidden_before':before_audit,'forbidden_after':after_audit},indent=2,sort_keys=True))

if __name__=='__main__': main()
