#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

VARIANTS = {"syntax_only", "syntax_algebra"}

OLD_COV = r'''noncomputable def covariantTotalLift
    (f : EtaCovariantLift) (tau : H) : InverseEtaTotal :=
  inverseEtaTotalMk tau (f : H -> ℂ) tau
'''
NEW_COV = r'''noncomputable def covariantTotalLift
    (f : EtaCovariantLift) (tau : H) : InverseEtaTotal :=
  inverseEtaTotalMk tau ((f : H -> ℂ) tau)
'''

OLD_COORD = r'''@[simp] theorem inverseEtaFibreCoordinate_smul
    {x : InverseEtaBase} (c : ℂ) (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (c • u) =
      c * inverseEtaFibreCoordinate u := by
  simpa only [smul_eq_mul] using
    (inverseEtaFibreCoordinateLinearEquiv x).map_smul c u
'''
NEW_COORD = r'''@[simp] theorem inverseEtaFibreCoordinate_smul
    {x : InverseEtaBase} (c : ℂ) (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (c • u) =
      c * inverseEtaFibreCoordinate u := by
  change (inverseEtaFibreCoordinateLinearEquiv x) (c • u) =
    c * (inverseEtaFibreCoordinateLinearEquiv x) u
  simpa only [smul_eq_mul] using
    (inverseEtaFibreCoordinateLinearEquiv x).map_smul c u
'''

OLD_HSMUL = r'''theorem inverseEtaFibreHermitian_smul_right
    {x : InverseEtaBase} (c : ℂ) (u v : InverseEtaFibre x) :
    inverseEtaFibreHermitian u (c • v) =
      c * inverseEtaFibreHermitian u v := by
  simp only [inverseEtaFibreHermitian,
    inverseEtaFibreCoordinate_smul, inner_smul_right]
'''
NEW_HSMUL = r'''theorem inverseEtaFibreHermitian_smul_right
    {x : InverseEtaBase} (c : ℂ) (u v : InverseEtaFibre x) :
    inverseEtaFibreHermitian u (c • v) =
      c * inverseEtaFibreHermitian u v := by
  unfold inverseEtaFibreHermitian
  rw [inverseEtaFibreCoordinate_smul]
  simpa only [smul_eq_mul] using
    (inner_smul_right (inverseEtaFibreCoordinate u)
      (inverseEtaFibreCoordinate v) c)
'''

OLD_POS = r'''theorem inverseEtaFibreHermitian_self_pos
    {x : InverseEtaBase} {u : InverseEtaFibre x} (hu : u ≠ 0) :
    0 < (inverseEtaFibreHermitian u u).re := by
  unfold inverseEtaFibreHermitian
  rw [re_inner_self_pos (𝕜 := ℂ)]
  intro hCoordinate
  apply hu
  apply (inverseEtaFibreCoordinateEquiv x).injective
  simpa using hCoordinate
'''
NEW_POS = r'''theorem inverseEtaFibreHermitian_self_pos
    {x : InverseEtaBase} {u : InverseEtaFibre x} (hu : u ≠ 0) :
    0 < (inverseEtaFibreHermitian u u).re := by
  rw [inverseEtaFibreHermitian_self_re]
  have hc : inverseEtaFibreCoordinate u ≠ 0 := by
    intro hCoordinate
    apply hu
    apply (inverseEtaFibreCoordinateEquiv x).injective
    simpa using hCoordinate
  have hn : 0 < ‖inverseEtaFibreCoordinate u‖ := norm_pos_iff.mpr hc
  nlinarith
'''

GATE = {
  "syntax_only": "/-- Exact invariance of the total-space lift. -/",
  "syntax_algebra": "/-! ## 9. Aggregate theorem and the exact remaining smooth-atlas statement -/",
}

def replace_once(text, old, new, label):
    if text.count(old) != 1:
        raise SystemExit(f"{label}: expected one match, got {text.count(old)}")
    return text.replace(old, new, 1)

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

def git_blob(data): return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def main():
    if len(sys.argv) != 3 or sys.argv[1] not in VARIANTS:
        raise SystemExit("usage: qym_gb79_v12_patch.py {syntax_only|syntax_algebra} QYM.lean")
    variant, path = sys.argv[1], Path(sys.argv[2])
    before = path.read_text(encoding="utf-8")
    before_audit = audit(before)
    text = replace_once(before, OLD_COV, NEW_COV, "covariantTotalLift")
    if variant == "syntax_algebra":
        text = replace_once(text, OLD_COORD, NEW_COORD, "coordinate_smul")
        text = replace_once(text, OLD_HSMUL, NEW_HSMUL, "Hermitian_smul_right")
        text = replace_once(text, OLD_POS, NEW_POS, "Hermitian_self_pos")
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f"forbidden-token delta {before_audit} -> {after_audit}")
    marker = GATE[variant]
    if marker not in text: raise SystemExit("gate marker missing")
    path.write_text(text, encoding="utf-8")
    raw = path.read_bytes()
    print(json.dumps({
      "schema":"qym-gb79-v12-patch-v1", "variant":variant,
      "candidate_sha256":hashlib.sha256(raw).hexdigest(), "candidate_blob":git_blob(raw),
      "gate_line":text.count("\n",0,text.index(marker))+1, "forbidden":after_audit,
      "bytes":len(raw), "lf":raw.count(b"\n")}, indent=2, sort_keys=True))

if __name__ == "__main__": main()
