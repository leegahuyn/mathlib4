#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys

PAT = {
"coord_of": re.compile(r"(?ms)^@\[simp\] theorem inverseEtaFibreOfCoordinate_coordinate\b.*?(?=^/-- Every actual quotient fibre is canonically equivalent)"),
"of_cont": re.compile(r"(?ms)^theorem inverseEtaFibreOfCoordinate_continuous\b.*?(?=^/-- Each actual quotient fibre is homeomorphic)"),
"smul": re.compile(r"(?ms)^@\[simp\] theorem inverseEtaFibreCoordinate_smul\b.*?(?=^/-- A local coordinate represented)"),
"mk0": re.compile(r"(?ms)^@\[simp\] theorem inverseEtaFibreMk_zero\b.*?(?=^@\[simp\] theorem inverseEtaFibreMk_add)"),
"mkadd": re.compile(r"(?ms)^@\[simp\] theorem inverseEtaFibreMk_add\b.*?(?=^@\[simp\] theorem inverseEtaFibreMk_smul)"),
"mksmul": re.compile(r"(?ms)^@\[simp\] theorem inverseEtaFibreMk_smul\b.*?(?=^/-! ## 6\.)"),
"hsmul": re.compile(r"(?ms)^theorem inverseEtaFibreHermitian_smul_right\b.*?(?=^/-- The real part on the diagonal)"),
"hpos": re.compile(r"(?ms)^theorem inverseEtaFibreHermitian_self_pos\b.*?(?=^/-- The Hermitian norm on the actual quotient total space)"),
"covtot": re.compile(r"(?ms)^noncomputable def covariantTotalLift\b.*?(?=^/-- Exact invariance of the total-space lift)"),
}
MARKER="/-- The fibre coordinate is continuous for the actual quotient-subspace\ntopology. -/\n"

COORD_OF=r'''@[simp] theorem inverseEtaFibreOfCoordinate_coordinate
    (x : InverseEtaBase) (u : InverseEtaFibre x) :
    inverseEtaFibreOfCoordinate x (inverseEtaFibreCoordinate u) = u := by
  apply Subtype.ext
  simpa [inverseEtaFibreOfCoordinate, inverseEtaFibreCoordinate, u.2] using
    totalOfBaseScalar_projection_coordinate u.1
'''
TOPO=r'''/-- Re-expose the actual fibre as the subtype of the quotient total space carrying
its inherited quotient-subspace topology. -/
noncomputable instance inverseEtaFibreTopologicalSpace (x : InverseEtaBase) :
    TopologicalSpace (InverseEtaFibre x) := by
  change TopologicalSpace
    {u : InverseEtaTotal // inverseEtaProjection u = x}
  infer_instance

'''
OF_CONT=r'''theorem inverseEtaFibreOfCoordinate_continuous (x : InverseEtaBase) :
    Continuous (inverseEtaFibreOfCoordinate x) := by
  have hTotal : Continuous
      (fun c : ℂ => totalOfBaseScalar x c) := by
    simpa [Function.comp_def] using
      totalOfBaseScalar_continuous.comp
        (continuous_const.prodMk continuous_id)
  change Continuous (fun c : ℂ =>
    (⟨totalOfBaseScalar x c,
      inverseEtaProjection_totalOfBaseScalar x c⟩ :
      {u : InverseEtaTotal // inverseEtaProjection u = x}))
  exact hTotal.subtype_mk
    (fun c => inverseEtaProjection_totalOfBaseScalar x c)
'''
SMUL_CHANGE=r'''@[simp] theorem inverseEtaFibreCoordinate_smul
    {x : InverseEtaBase} (c : ℂ) (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (c • u) =
      c * inverseEtaFibreCoordinate u := by
  change (inverseEtaFibreCoordinateLinearEquiv x) (c • u) =
    c * (inverseEtaFibreCoordinateLinearEquiv x) u
  simpa only [smul_eq_mul] using
    (inverseEtaFibreCoordinateLinearEquiv x).map_smul c u
'''
SMUL_SIMP=r'''@[simp] theorem inverseEtaFibreCoordinate_smul
    {x : InverseEtaBase} (c : ℂ) (u : InverseEtaFibre x) :
    inverseEtaFibreCoordinate (c • u) =
      c * inverseEtaFibreCoordinate u := by
  simpa [inverseEtaFibreCoordinateLinearEquiv, smul_eq_mul] using
    (inverseEtaFibreCoordinateLinearEquiv x).map_smul c u
'''
MK0=r'''@[simp] theorem inverseEtaFibreMk_zero (tau : H) :
    inverseEtaFibreMk tau 0 =
      (0 : InverseEtaFibre
        (Mock2.Definition15Geometry.quotientMap tau)) := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  rw [inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_zero]
  simp
'''
MKADD=r'''@[simp] theorem inverseEtaFibreMk_add
    (tau : H) (z w : ℂ) :
    inverseEtaFibreMk tau (z + w) =
      inverseEtaFibreMk tau z + inverseEtaFibreMk tau w := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  rw [inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_add,
    inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_mk]
  ring
'''
MKSMUL=r'''@[simp] theorem inverseEtaFibreMk_smul
    (tau : H) (c z : ℂ) :
    inverseEtaFibreMk tau (c * z) =
      c • inverseEtaFibreMk tau z := by
  apply (inverseEtaFibreCoordinateEquiv _).injective
  rw [inverseEtaFibreCoordinate_mk, inverseEtaFibreCoordinate_smul,
    inverseEtaFibreCoordinate_mk]
  ring
'''
HSMUL=r'''theorem inverseEtaFibreHermitian_smul_right
    {x : InverseEtaBase} (c : ℂ) (u v : InverseEtaFibre x) :
    inverseEtaFibreHermitian u (c • v) =
      c * inverseEtaFibreHermitian u v := by
  simpa [inverseEtaFibreHermitian, inverseEtaFibreCoordinate_smul,
    smul_eq_mul] using
      (inner_smul_right (inverseEtaFibreCoordinate u) c
        (inverseEtaFibreCoordinate v))
'''
HPOS=r'''theorem inverseEtaFibreHermitian_self_pos
    {x : InverseEtaBase} {u : InverseEtaFibre x} (hu : u ≠ 0) :
    0 < (inverseEtaFibreHermitian u u).re := by
  rw [inverseEtaFibreHermitian_self_re]
  have hcoord : inverseEtaFibreCoordinate u ≠ 0 := by
    intro h
    apply hu
    apply (inverseEtaFibreCoordinateEquiv x).injective
    simpa using h
  have hn : 0 < ‖inverseEtaFibreCoordinate u‖ := norm_pos_iff.mpr hcoord
  nlinarith
'''
COVTOT=r'''noncomputable def covariantTotalLift
    (f : EtaCovariantLift) (tau : H) : InverseEtaTotal :=
  inverseEtaTotalMk tau ((f : H -> ℂ) tau)
'''

VARIANTS={"change":SMUL_CHANGE,"simp":SMUL_SIMP}

def repl(text,key,new):
  ms=list(PAT[key].finditer(text))
  if len(ms)!=1: raise SystemExit(f"{key} matches={len(ms)}")
  m=ms[0]; return text[:m.start()]+new.rstrip()+"\n\n"+text[m.end():]
def audit(text):
  return {"sorry":len(re.findall(r"\bsorry\b",text)),"admit":len(re.findall(r"\badmit\b",text)),"native_decide":len(re.findall(r"\bnative_decide\b",text)),"Lean.ofReduceBool":text.count("Lean.ofReduceBool"),"global_axiom":len(re.findall(r"(?m)^\s*axiom\s+",text)),"unsafe":len(re.findall(r"(?m)^\s*unsafe\s+",text)),"maxHeartbeats_zero":len(re.findall(r"set_option\s+maxHeartbeats\s+0\b",text))}

def main():
  if len(sys.argv)!=3 or sys.argv[1] not in VARIANTS: raise SystemExit("usage: inverseeta_patch VARIANT QYM.lean")
  variant,p=sys.argv[1],Path(sys.argv[2]); before=p.read_bytes(); text=before.decode(); a0=audit(text)
  text=repl(text,"coord_of",COORD_OF)
  if text.count(MARKER)!=1: raise SystemExit("topology marker mismatch")
  text=text.replace(MARKER,TOPO+MARKER,1)
  text=repl(text,"of_cont",OF_CONT)
  text=repl(text,"smul",VARIANTS[variant])
  text=repl(text,"mk0",MK0); text=repl(text,"mkadd",MKADD); text=repl(text,"mksmul",MKSMUL)
  text=repl(text,"hsmul",HSMUL); text=repl(text,"hpos",HPOS); text=repl(text,"covtot",COVTOT)
  a1=audit(text)
  if a1!=a0: raise SystemExit(f"forbidden delta {a0}->{a1}")
  p.write_text(text); after=p.read_bytes()
  print(json.dumps({"variant":variant,"input_sha256":hashlib.sha256(before).hexdigest(),"candidate_sha256":hashlib.sha256(after).hexdigest(),"forbidden":a1},indent=2,sort_keys=True))
if __name__=="__main__": main()
