#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

BASE_SHA256 = "790b40c05a8f3735dd171a135eda65de92ab68b247d13e7e2ffe2968e3798421"
BASE_BLOB = "33e4fab1130e4c17ea5d212fe2691c3e0c0eb8d3"
VARIANTS = {"edge_only": 1, "edge_re": 2, "edge_both": 3}

OLD_EDGE = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  simpa [QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport] using
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''
NEW_EDGE = r'''theorem edgeParameterTransport_hasDerivAt
    (e : QYM.FullCertification.PolygonTraceExtension.PolygonEdge) (t : ℝ) :
    HasDerivAt (QYM.FullCertification.P2NormalGreenExtension.edgeParameterTransport e)
      (e.2.parameterSign : ℝ) t := by
  letI : AddCommGroup ℝ := Real.instAddCommGroup
  letI : Module ℝ ℝ := Semiring.toModule
  change HasDerivAt
    (fun x : ℝ => (e.2.parameterSign : ℝ) * x)
    (e.2.parameterSign : ℝ) t
  simpa only [id_eq, mul_one] using
    (hasDerivAt_id t).const_mul (e.2.parameterSign : ℝ)
'''

OLD_RE = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  simp [hyperbolicRightNormal, Complex.mul_re, Complex.mul_im]
  ring_nf
'''
NEW_RE = r'''theorem conj_mul_hyperbolicRightNormal_realMultiple_re
    (y s : ℝ) (v : ℂ) :
    (star v *
      hyperbolicRightNormal y (((s : ℝ) : ℂ) * v)).re = 0 := by
  have hstar : star v * v = (Complex.normSq v : ℂ) := by
    change conj v * v = (Complex.normSq v : ℂ)
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [hyperbolicRightNormal,
    show star v *
        ((((y / ‖(((s : ℝ) : ℂ) * v)‖ : ℝ) : ℂ) * (-Complex.I)) *
          (((s : ℝ) : ℂ) * v)) =
      ((((y / ‖(((s : ℝ) : ℂ) * v)‖ : ℝ) : ℂ) * (-Complex.I)) *
        ((s : ℝ) : ℂ)) * (star v * v) by ring,
    hstar]
  simp [Complex.mul_re, Complex.normSq_eq_norm_sq]
'''

OLD_IM = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
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
NEW_IM = r'''theorem conj_mul_hyperbolicRightNormal_im {y : ℝ} {w : ℂ}
    (hw : w ≠ 0) :
    (star w * hyperbolicRightNormal y w).im =
      -y * ‖w‖ := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hstar : star w * w = (Complex.normSq w : ℂ) := by
    change conj w * w = (Complex.normSq w : ℂ)
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [hyperbolicRightNormal,
    show star w * ((((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) * w) =
        (((y / ‖w‖ : ℝ) : ℂ) * (-Complex.I)) *
          (star w * w) by ring,
    hstar]
  simp [Complex.mul_im, Complex.normSq_eq_norm_sq]
  field_simp [hn]
  <;> ring
'''

GATE_MARKERS = {
    "edge_only": "/-- Exact derivative of the transported target curve. -/",
    "edge_re": "/-- Exact signed-area formula for the right normal. -/",
    "edge_both": "/-! ## 2. The actual geometric normal and its three unconditional laws -/",
}

def sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def blob(b: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()

def audit(t: str):
    return {
        "sorry": len(re.findall(r"\bsorry\b", t)),
        "admit": len(re.findall(r"\badmit\b", t)),
        "native_decide": len(re.findall(r"\bnative_decide\b", t)),
        "Lean.ofReduceBool": t.count("Lean.ofReduceBool"),
        "global_axiom": len(re.findall(r"(?m)^\s*axiom\s+", t)),
        "unsafe": len(re.findall(r"(?m)^\s*unsafe\s+", t)),
        "maxHeartbeats_zero": len(re.findall(r"set_option\s+maxHeartbeats\s+0\b", t)),
    }

def replace_once(t: str, old: str, new: str, label: str) -> str:
    n = t.count(old)
    if n != 1:
        raise SystemExit(f"{label}: expected one exact match, got {n}")
    return t.replace(old, new, 1)

def main():
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit("usage: qym_patch_gb79_v11_1.py {edge_only|edge_re|edge_both} QYM.lean")
    variant = sys.argv[1]
    p = Path(sys.argv[2])
    before = p.read_bytes()
    if sha256(before) != BASE_SHA256 or blob(before) != BASE_BLOB:
        raise SystemExit(f"unexpected GB79 input identity: {sha256(before)} {blob(before)}")
    t = before.decode("utf-8")
    a0 = audit(t)
    t = replace_once(t, OLD_EDGE, NEW_EDGE, "edge theorem")
    if VARIANTS[variant] >= 2:
        t = replace_once(t, OLD_RE, NEW_RE, "real-multiple normal theorem")
    if VARIANTS[variant] >= 3:
        t = replace_once(t, OLD_IM, NEW_IM, "imaginary normal theorem")
    a1 = audit(t)
    if a1 != a0:
        raise SystemExit(f"forbidden-token delta: {a0} -> {a1}")
    marker = GATE_MARKERS[variant]
    if marker not in t:
        raise SystemExit("gate marker missing")
    p.write_text(t, encoding="utf-8")
    out = p.read_bytes()
    print(json.dumps({
        "schema": "qym-gb79-v11-1-patch-v1",
        "variant": variant,
        "input_sha256": BASE_SHA256,
        "input_blob": BASE_BLOB,
        "candidate_sha256": sha256(out),
        "candidate_blob": blob(out),
        "gate_line": t.count("\n", 0, t.index(marker)) + 1,
        "forbidden": a1,
        "bytes": len(out),
        "lf": out.count(b"\n"),
    }, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
