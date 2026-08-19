#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

BASE_SHA256 = "790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421"

EDGE_RE = re.compile(r"(?ms)^theorem edgeParameterTransport_hasDerivAt\b.*?(?=^/-- Exact derivative of the transported target curve)" )
C8_RE = re.compile(r"(?ms)^theorem conj_mul_hyperbolicRightNormal_realMultiple_re\b.*?(?=^/-- Exact signed-area formula)" )
C9_RE = re.compile(r"(?ms)^theorem conj_mul_hyperbolicRightNormal_im\b.*?(?=^/-! ## 2\. The actual geometric normal)" )

EDGE_SIMPA = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  letI : AddCommGroup ℝ := Real.instAddCommGroup
  letI : Module ℝ ℝ := Semiring.toModule
  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''

EDGE_CHANGE = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  letI : AddCommGroup ℝ := Real.instAddCommGroup
  letI : Module ℝ ℝ := Semiring.toModule
  change HasDerivAt (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  exact (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
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
  · have horth := conj_mul_hyperbolicRightNormal_re y (((s : ℝ) : ℂ) * v)
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

VARIANTS = {
  "simpa_direct": (EDGE_SIMPA, C8_DIRECT),
  "change_direct": (EDGE_CHANGE, C8_DIRECT),
  "change_structural": (EDGE_CHANGE, C8_STRUCTURAL),
}

def replace_one(text, pattern, replacement, label):
    ms=list(pattern.finditer(text))
    if len(ms)!=1: raise SystemExit(f"{label}: expected 1 match, got {len(ms)}")
    m=ms[0]
    return text[:m.start()] + replacement.rstrip() + "\n\n" + text[m.end():]

def audit(text):
    return {
      "sorry": len(re.findall(r"\bsorry\b", text)),
      "admit": len(re.findall(r"\badmit\b", text)),
      "native_decide": len(re.findall(r"\bnative_decide\b", text)),
      "Lean.ofReduceBool": text.count("Lean.ofReduceBool"),
      "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", text)),
      "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", text)),
      "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", text)),
    }

def main():
    if len(sys.argv)!=3 or sys.argv[1] not in VARIANTS:
        raise SystemExit("usage: qym_gb79_v11_patch.py VARIANT QYM.lean")
    variant, fn=sys.argv[1], Path(sys.argv[2])
    raw=fn.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=BASE_SHA256: raise SystemExit("unexpected GB79 SHA256")
    text=raw.decode("utf-8"); before=audit(text)
    edge,c8=VARIANTS[variant]
    text=replace_one(text,EDGE_RE,edge,"edge")
    text=replace_one(text,C8_RE,c8,"c8")
    text=replace_one(text,C9_RE,C9,"c9")
    after=audit(text)
    if after!=before: raise SystemExit(f"forbidden delta: {before} -> {after}")
    fn.write_text(text,encoding="utf-8")
    out=fn.read_bytes()
    print(json.dumps({"variant":variant,"input_sha256":BASE_SHA256,
      "candidate_sha256":hashlib.sha256(out).hexdigest(),"bytes":len(out),"forbidden":after},indent=2,sort_keys=True))

if __name__=="__main__": main()
