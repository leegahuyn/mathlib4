#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib,json,re,sys

BASELINE_SHA256='313c076645a51976237738bd10c7f22b54f2a483499e60b57fa0d69be007cc1e'
BASELINE_BLOB='ff49510790dd7ca136bf34c3ec7150617ee1c241'
VARIANTS={'derive_and_star','coordinate_star','derive_and_normsq'}

OLD_REAL='''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im]
  ring_nf
'''

REAL_DERIVE='''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  by_cases hs : s = 0
  · subst s
    simp [hyperbolicRightNormal]
  · have h := conj_mul_hyperbolicRightNormal_re y (((s : ℝ) : ℂ) * v)
    have hscale :
        s * (star v *
          hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
      simpa [map_mul, mul_assoc, Complex.mul_re] using h
    exact (mul_eq_zero.mp hscale).resolve_left hs
'''

REAL_COORD='''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.inv_re, Complex.inv_im]
  ring
'''

OLD_IM='''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub,
    pow_two]
  field_simp [hn]
  <;> ring_nf
'''

IM_STAR='''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring]
  simp only [Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub]
  rw [← Complex.sq_norm w]
  field_simp [hn]
  ring
'''

IM_NORMSQ='''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring]
  have hsq : (star w * w).re = ‖w‖ ^ 2 := by
    simp [Complex.mul_re, Complex.star_def, Complex.sq_norm,
      Complex.normSq_apply]
  have him : (star w * w).im = 0 := by
    simp [Complex.mul_im, Complex.star_def]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, mul_zero, zero_mul, sub_zero, zero_sub, hsq, him]
  field_simp [hn]
  ring
'''

def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def audit(t): return {'sorry':len(re.findall(r'\bsorry\b',t)),'admit':len(re.findall(r'\badmit\b',t)),'native_decide':len(re.findall(r'\bnative_decide\b',t)),'Lean.ofReduceBool':t.count('Lean.ofReduceBool'),'global_axiom':len(re.findall(r'(?m)^\s*axiom\s+',t)),'unsafe':len(re.findall(r'(?m)^\s*unsafe\s+',t)),'maxHeartbeats_zero':len(re.findall(r'set_option\s+maxHeartbeats\s+0\b',t))}

def main():
    if len(sys.argv)!=3 or sys.argv[1] not in VARIANTS: raise SystemExit('usage: qym_c05_variants.py VARIANT QYM.lean')
    v,p=sys.argv[1],Path(sys.argv[2]); before=p.read_bytes()
    if hashlib.sha256(before).hexdigest()!=BASELINE_SHA256 or blob(before)!=BASELINE_BLOB: raise SystemExit('baseline mismatch')
    text=before.decode(); a0=audit(text)
    real=REAL_COORD if v=='coordinate_star' else REAL_DERIVE
    im=IM_NORMSQ if v=='derive_and_normsq' else IM_STAR
    for label,old,new in [('realMultiple',OLD_REAL,real),('imaginary',OLD_IM,im)]:
        if text.count(old)!=1: raise SystemExit(f'{label} count={text.count(old)}')
        text=text.replace(old,new,1)
    a1=audit(text)
    if a1!=a0: raise SystemExit(f'forbidden delta {a0}->{a1}')
    p.write_text(text); after=p.read_bytes()
    print(json.dumps({'schema':'qym-c05-v1','variant':v,'input_sha256':BASELINE_SHA256,'input_blob':BASELINE_BLOB,'candidate_sha256':hashlib.sha256(after).hexdigest(),'candidate_blob':blob(after),'bytes':len(after),'lf':after.count(b'\n'),'fixed_producers_targeted':['conj_mul_hyperbolicRightNormal_realMultiple_re','conj_mul_hyperbolicRightNormal_im'],'forbidden_before':a0,'forbidden_after':a1},indent=2,sort_keys=True))
if __name__=='__main__': main()
