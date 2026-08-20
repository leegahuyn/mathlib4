#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib, json, re, sys

C4 = r'''theorem baseEdgeCoordinate_hasDerivAt
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
            (fun s : ℝ => ((Real.sqrt (1 - (s / 2) ^ 2) : ℝ) : ℂ))
            ((-t / (4 * Real.sqrt (1 - (t / 2) ^ 2)) : ℝ) : ℂ) t :=
        (hasDerivAt_circularHeight ht).ofReal_comp
      change HasDerivAt
        (fun s : ℝ => Complex.mk (s / 2) (Real.sqrt (1 - (s / 2) ^ 2)))
        (Complex.mk ((1 : ℝ) / 2)
          (-t / (4 * Real.sqrt (1 - (t / 2) ^ 2)))) t
      simpa [Complex.mk_eq_add_mul_I] using hx.add (hy.mul_const Complex.I)
  | leftVerticalSegment =>
      have hconst : HasDerivAt
          (fun _ : ℝ =>
            (-((1 : ℝ) / 2) : ℂ) +
              ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) 0 t :=
        hasDerivAt_const t _
      have hlin : HasDerivAt
          (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I)
      change HasDerivAt
        (fun s : ℝ => Complex.mk (-((1 : ℝ) / 2)) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa [Complex.mk_eq_add_mul_I, add_mul, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using hconst.add hlin
  | rightVerticalSegment =>
      have hconst : HasDerivAt
          (fun _ : ℝ =>
            (((1 : ℝ) / 2 : ℝ) : ℂ) +
              ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) 0 t :=
        hasDerivAt_const t _
      have hlin : HasDerivAt
          (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
        simpa using ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I)
      change HasDerivAt
        (fun s : ℝ => Complex.mk ((1 : ℝ) / 2) (Real.sqrt 3 / 2 + s))
        Complex.I t
      simpa [Complex.mk_eq_add_mul_I, add_mul, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using hconst.add hlin
'''

C5 = r'''theorem selectedRepresentativeChart_hasStrictDerivAt
    (q : Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.GammaTwoRightCoset) (z : ℍ) :
    HasStrictDerivAt (selectedRepresentativeChart q)
      (1 / selectedRepresentativeDenom q (z : ℂ) ^ 2) (z : ℂ) := by
  letI : AddCommGroup ℂ := Complex.addCommGroup
  have hdet : (selectedRepresentativeRealMatrix q).val.det = 1 := by
    simp [selectedRepresentativeRealMatrix]
  have h :=
    UpperHalfPlane.hasStrictDerivAt_smul
      (g := selectedRepresentativeRealMatrix q) (by
        change 0 <
          (((Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q :
            SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det
        exact
          Mock2FA.PaperCorrections.AutomorphicSobolev.FixedPhaseIntrinsicAdjointCutoff.integralMoebius_det_pos
            (Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.gammaTwoCosetRep q)) z
  simpa [selectedRepresentativeChart, selectedRepresentativeCoordinate,
    selectedRepresentativeDenom, selectedRepresentativeRealMatrix,
    hdet, one_div] using h
'''

C6 = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  letI : AddCommGroup ℝ := Real.instAddCommGroup
  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''

PATTERNS = [
 (re.compile(r'(?ms)^theorem baseEdgeCoordinate_hasDerivAt\b.*?(?=^/-! ## 4\. Transport)'), C4, 'c4'),
 (re.compile(r'(?ms)^theorem selectedRepresentativeChart_hasStrictDerivAt\b.*?(?=^/-- Fully explicit complex coordinate)'), C5, 'c5'),
 (re.compile(r'(?ms)^theorem edgeParameterTransport_hasDerivAt\b.*?(?=^/-- Exact derivative of the transported target curve)'), C6, 'c6'),
]

def blob(b: bytes) -> str:
 return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

def main():
 if len(sys.argv)!=2: raise SystemExit('usage: qym_patch_c4_c6.py QYM.lean')
 p=Path(sys.argv[1]); before=p.read_bytes(); text=before.decode()
 for pat,repl,label in PATTERNS:
  ms=list(pat.finditer(text))
  if len(ms)!=1: raise SystemExit(f'{label}: expected one match, found {len(ms)}')
  m=ms[0]; text=text[:m.start()]+repl+'\n'+text[m.end():]
 p.write_text(text)
 after=p.read_bytes(); s=after.decode()
 forbidden={'sorry':len(re.findall(r'\bsorry\b',s)),'admit':len(re.findall(r'\badmit\b',s)),
 'native_decide':len(re.findall(r'\bnative_decide\b',s)),'Lean.ofReduceBool':s.count('Lean.ofReduceBool'),
 'global_axiom':len(re.findall(r'(?m)^\s*axiom\s+',s)),'unsafe':len(re.findall(r'(?m)^\s*unsafe\s+',s)),
 'maxHeartbeats_zero':len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',s))}
 if any(forbidden.values()): raise SystemExit(f'forbidden audit failed: {forbidden}')
 marker='/-- Exact derivative of the transported target curve. -/'
 gate=s.count('\n',0,s.index(marker))+1
 print(json.dumps({'schema':'qym-c4-c6-v1','input_sha256':hashlib.sha256(before).hexdigest(),
 'input_blob':blob(before),'candidate_sha256':hashlib.sha256(after).hexdigest(),'candidate_blob':blob(after),
 'bytes':len(after),'lf':after.count(b'\n'),'gate_line':gate,'forbidden':forbidden},indent=2,sort_keys=True))

if __name__=='__main__': main()
