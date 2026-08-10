#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
BASE_SHA = "1f0a7e6c95691a89b3099a829da3e11fbbc731332f87e7c63d24eadade5692eb"
BASE_LINES = 60450
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)", re.MULTILINE)

spec = importlib.util.spec_from_file_location(
    "fa459_base", ROOT / "scripts/fa459_prepare_true_first_cluster.py")
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA459 preparer")
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)

PROTECTED = [
    "actualEdgeAmbientParam_hasDerivAt",
    "nativeActualEdgeFluxIntegral_paired_circular",
    "nativeActualEdgeFluxIntegral_paired_left",
    "nativeActualEdgeFluxIntegral_paired_right",
    "selectedHalfOpenTile_ae_eq_openTile",
    "integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola",
    "fixedPhaseEuclideanGauge_lower_pred",
    "height_mul_dx_eq_negI_half_raise_sub_lower_sub",
    "norm_height_mul_dx_le_euclideanGraph",
    "selectedCosetConformalScaleC_realSmooth",
    "selectedCosetConformalScaleC_eq_inv_normSq_denom",
    "norm_selectedCosetConformalScaleC_eq_derivative",
    "norm_selectedCosetA_le_scale",
    "norm_selectedCosetB_le_scale",
    "dx_selectedCosetUnitaryPullback",
    "dy_selectedCosetUnitaryPullback",
    "height_mul_dy_selectedCosetUnitaryPullback",
    "norm_height_mul_dy_selectedCosetUnitaryPullback_le",
    "logHeightTraceDrift_nonneg",
    "height_mul_normSq_selectedCuspPulledEuclideanGauge",
    "normSq_selectedCuspRestrictionRepresentative_eq_height_mul_pulled",
    "selectedHorocycleL2_norm_sq_eq_integral",
]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def span(text: str, name: str) -> tuple[int, int]:
    matches = list(DECL_RE.finditer(text))
    for i,m in enumerate(matches):
        if m.group(1) == name:
            return m.start(), matches[i+1].start() if i+1 < len(matches) else len(text)
    raise RuntimeError(f"declaration not found: {name}")


def header(text: str, name: str) -> str:
    a,b = span(text,name)
    block=text[a:b]
    p=block.find(":=")
    if p < 0: raise RuntimeError(f"assignment not found: {name}")
    return block[:p+2]


def replace_body(text: str, name: str, proof: str) -> str:
    a,b=span(text,name); block=text[a:b]; p=block.find(":=")
    if p < 0: raise RuntimeError(f"assignment not found: {name}")
    suffix="\n" if block.endswith("\n") else ""
    return text[:a]+block[:p+2]+" "+proof.rstrip()+"\n"+suffix+text[b:]


def replace_in_decl(text: str, name: str, old: str, new: str) -> str:
    a,b=span(text,name); block=text[a:b]; count=block.count(old)
    if count != 1:
        raise RuntimeError(f"{name}: expected one replacement, found {count}: {old!r}")
    return text[:a]+block.replace(old,new,1)+text[b:]


GL_SELECTED_AE = """by
  change selectedCosetGL q • modularHalfOpenTile =ᵐ[hyperbolicMeasure]
    selectedCosetGL q • ModularGroup.fdo
  exact Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq
    (selectedCosetGL q)
    (measurePreserving_smul (selectedCosetGL q)⁻¹
      hyperbolicMeasure).quasiMeasurePreserving
    modularHalfOpenTile_ae_eq_fdo"""

HSELECTED_OLD = """  have hSelectedTile : MeasurableSet
      (gammaTwoCosetRep q • modularHalfOpenTile) :=
    MeasurableSet.const_smul modularHalfOpenTile_measurable
      (gammaTwoCosetRep q)"""
HSELECTED_GL = """  have hSelectedTile : MeasurableSet
      (gammaTwoCosetRep q • modularHalfOpenTile) := by
    change MeasurableSet (selectedCosetGL q • modularHalfOpenTile)
    exact MeasurableSet.const_smul modularHalfOpenTile_measurable
      (selectedCosetGL q)"""

LOWER_PRED_A = """by
  have hScale := euclideanGaugeScale_succ (n - 1) z
  have hExponent := euclideanGaugeExponent_succ (n - 1)
  rw [sub_add_cancel] at hScale hExponent
  simp only [fixedPhaseEuclideanGauge_apply,
    InverseEtaFixedPhaseCore.lower_apply]
  unfold euclideanLowerFromSuccGauge lowerRaw
  rw [dx_fixedPhaseEuclideanGauge,
    dy_fixedPhaseEuclideanGauge,
    hScale, hExponent,
    complex_rpow_derivative_eq_div,
    fixedPhaseEuclideanGauge_apply]
  have hz : heightC z ≠ 0 :=
    Complex.ofReal_ne_zero.mpr z.im_ne_zero
  field_simp [hz]
  push_cast
  ring"""

HORIZONTAL_A = """by
  rw [euclideanRaiseGauge_sub_lowerPredGauge]
  ring_nf
  simp only [Complex.I_sq]
  ring"""

HORIZONTAL_B = """by
  rw [euclideanRaiseGauge_sub_lowerPredGauge]
  change heightC z * dx f z =
    (-Complex.I / 2) * (2 * Complex.I * heightC z * dx f z)
  calc
    _ = (1 : ℂ) * (heightC z * dx f z) := by ring
    _ = _ := by ring"""

SCALE_EQ = """by
  unfold selectedCosetConformalScaleC selectedCosetAction heightC
  change
    (((selectedCosetGL q • z).im : ℂ) / (z.im : ℂ)) =
      ((1 / Complex.normSq
        (UpperHalfPlane.denom (selectedCosetGL q) z) : ℝ) : ℂ)
  rw [UpperHalfPlane.im_smul_eq_div_normSq, selectedCosetGL_det]
  simp only [abs_one, one_mul, Complex.ofReal_div, Complex.ofReal_one]
  field_simp [z.im_ne_zero]"""

NORM_DERIV = """by
  have hden := selectedCosetDenom_ne_zero q z
  have hnorm : 0 < ‖selectedCosetDenom q z‖ := norm_pos_iff.mpr hden
  rw [selectedCosetConformalScaleC_eq_inv_normSq_denom]
  change
    ‖((1 / Complex.normSq (selectedCosetDenom q z) : ℝ) : ℂ)‖ =
      ‖1 / selectedCosetDenom q z ^ 2‖
  rw [Complex.norm_real, abs_of_pos (one_div_pos.mpr
    (Complex.normSq_pos.mpr hden)), norm_div, norm_one, norm_pow,
    Complex.normSq_eq_norm_sq]"""

LOG_DRIFT = """by
  unfold logHeightTraceDrift
  have hDrift : 0 ≤ euclideanHorizontalDrift n :=
    euclideanHorizontalDrift_nonneg n
  linarith"""

L2_NORM = """by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) F,
    MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner F F)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t =>
    inner_self_eq_norm_sq (𝕜 := ℂ) (F t)"""


def apply_gl_pair_cumulative(text: str) -> tuple[str,list[dict[str,str]]]:
    repairs=[]
    text,r=base.apply_pair_compat(text,"macro"); repairs.append(r)
    text=replace_body(text,"selectedHalfOpenTile_ae_eq_openTile",GL_SELECTED_AE)
    repairs.append({"declaration":"selectedHalfOpenTile_ae_eq_openTile","strategy":"selectedCosetGL_invariant_measure"})
    text=replace_in_decl(text,"integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola",
        HSELECTED_OLD,HSELECTED_GL)
    repairs.append({"declaration":"integrableOn_heightSq_divergence_selectedHalfOpenTile_iff_basePiola","strategy":"selectedCosetGL_measurable_const_smul"})
    text,rs=base.fa458.apply_cumulative(text,"direct_union")
    repairs.extend(rs)
    return text,repairs


def apply_algebra(text: str, horizontal: str) -> tuple[str,list[dict[str,str]]]:
    repairs=[]
    text=replace_body(text,"fixedPhaseEuclideanGauge_lower_pred",LOWER_PRED_A)
    repairs.append({"declaration":"fixedPhaseEuclideanGauge_lower_pred","strategy":"mirror_proven_lowerFromSucc_proof_with_fixedPhase_apply"})
    text=replace_body(text,"height_mul_dx_eq_negI_half_raise_sub_lower_sub",
        HORIZONTAL_A if horizontal=="A" else HORIZONTAL_B)
    repairs.append({"declaration":"height_mul_dx_eq_negI_half_raise_sub_lower_sub","strategy":f"explicit_complex_I_algebra_{horizontal}"})
    text=replace_in_decl(text,"norm_height_mul_dx_le_euclideanGraph",
        "exact add_le_add_right (norm_sub_le _ _) _",
        "exact add_le_add (norm_sub_le _ _) (le_refl _)")
    repairs.append({"declaration":"norm_height_mul_dx_le_euclideanGraph","strategy":"fully_typed_add_le_add"})
    return text,repairs


def apply_cluster1(text: str) -> tuple[str,list[dict[str,str]]]:
    repairs=[]
    for name,old,new in [
        ("selectedCosetConformalScaleC_realSmooth",
         "realSmooth_heightC.inv (fun z => heightC_ne_zero z)",
         "RealSmooth.inv realSmooth_heightC (fun z => heightC_ne_zero z)"),
        ("dx_selectedCosetConformalScaleC",
         "realSmooth_heightC.inv (fun w => heightC_ne_zero w)",
         "RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)"),
        ("dy_selectedCosetConformalScaleC",
         "realSmooth_heightC.inv (fun w => heightC_ne_zero w)",
         "RealSmooth.inv realSmooth_heightC (fun w => heightC_ne_zero w)"),
    ]:
        text=replace_in_decl(text,name,old,new)
    repairs.append({"declaration":"selectedCosetConformalScaleC_realSmooth/dx/dy","strategy":"fully_qualified_RealSmooth_inv"})
    text=replace_body(text,"selectedCosetConformalScaleC_eq_inv_normSq_denom",SCALE_EQ)
    repairs.append({"declaration":"selectedCosetConformalScaleC_eq_inv_normSq_denom","strategy":"selectedCosetGL_im_smul_formula"})
    text=replace_body(text,"norm_selectedCosetConformalScaleC_eq_derivative",NORM_DERIV)
    repairs.append({"declaration":"norm_selectedCosetConformalScaleC_eq_derivative","strategy":"fold_selectedCosetDenom_before_norm_rewrite"})
    text=replace_in_decl(text,"norm_selectedCosetA_le_scale",
        "simp only [selectedCosetA, Complex.norm_real]",
        "simp only [selectedCosetA, Complex.norm_real, Real.norm_eq_abs]")
    text=replace_in_decl(text,"norm_selectedCosetB_le_scale",
        "simp only [selectedCosetB, Complex.norm_real]",
        "simp only [selectedCosetB, Complex.norm_real, Real.norm_eq_abs]")
    repairs.append({"declaration":"norm_selectedCosetA/B_le_scale","strategy":"real_norm_to_abs"})
    text=replace_in_decl(text,"norm_height_mul_dy_selectedCosetConformalScaleC_le",
        "exact add_le_add_right (norm_selectedCosetA_le_scale q z) _",
        "simpa [add_comm] using add_le_add_right (norm_selectedCosetA_le_scale q z) ‖selectedCosetConformalScaleC q z‖")
    repairs.append({"declaration":"norm_height_mul_dy_selectedCosetConformalScaleC_le","strategy":"normalize_add_order"})
    text=replace_in_decl(text,"dx_selectedCosetUnitaryPullback",
        "  rw [dx_mul (selectedCosetConformalScaleC_realSmooth q)",
        "  unfold selectedCosetUnitaryPullback\n  rw [dx_mul (selectedCosetConformalScaleC_realSmooth q)")
    text=replace_in_decl(text,"dy_selectedCosetUnitaryPullback",
        "  rw [dy_mul (selectedCosetConformalScaleC_realSmooth q)",
        "  unfold selectedCosetUnitaryPullback\n  rw [dy_mul (selectedCosetConformalScaleC_realSmooth q)")
    repairs.append({"declaration":"dx/dy_selectedCosetUnitaryPullback","strategy":"unfold_before_product_rule"})
    text=replace_in_decl(text,"height_mul_dy_selectedCosetUnitaryPullback",
        "  rw [dy_selectedCosetUnitaryPullback q hf,\n    height_mul_dy_selectedCosetConformalScaleC]\n",
        "  rw [dy_selectedCosetUnitaryPullback q hf]\n  rw [mul_add, ← mul_assoc, height_mul_dy_selectedCosetConformalScaleC]\n")
    repairs.append({"declaration":"height_mul_dy_selectedCosetUnitaryPullback","strategy":"distribute_associate_before_scale_rewrite"})
    text=replace_in_decl(text,"norm_height_mul_dy_selectedCosetUnitaryPullback_le",
        "_ ≤ ‖S‖ + ‖S‖ := add_le_add_right hA _",
        "_ ≤ ‖S‖ + ‖S‖ := by simpa [add_comm] using add_le_add_right hA ‖S‖")
    repairs.append({"declaration":"norm_height_mul_dy_selectedCosetUnitaryPullback_le","strategy":"normalize_add_order"})
    text=replace_body(text,"logHeightTraceDrift_nonneg",LOG_DRIFT)
    repairs.append({"declaration":"logHeightTraceDrift_nonneg","strategy":"use_existing_horizontal_drift_nonneg"})
    text=replace_in_decl(text,"height_mul_normSq_selectedCuspPulledEuclideanGauge",
        "Complex.norm_real, abs_of_pos (Real.rpow_pos_of_pos hz _)",
        "Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hz _)")
    text=replace_in_decl(text,"normSq_selectedCuspRestrictionRepresentative_eq_height_mul_pulled",
        "Complex.norm_real,\n      abs_of_pos (selectedCuspTraceWeight_pos n q Y t)",
        "Real.norm_eq_abs,\n      abs_of_pos (selectedCuspTraceWeight_pos n q Y t)")
    repairs.append({"declaration":"selected cusp norm normalizations","strategy":"real_norm_to_abs"})
    text=replace_body(text,"selectedHorocycleL2_norm_sq_eq_integral",L2_NORM)
    repairs.append({"declaration":"selectedHorocycleL2_norm_sq_eq_integral","strategy":"explicit_complex_inner_scalar"})
    return text,repairs


def main() -> None:
    p=argparse.ArgumentParser()
    p.add_argument("--variant",required=True,choices=[
        "baseline","gl_cumulative","gl_algA","gl_algB","gl_cluster1A","gl_cluster1B"])
    p.add_argument("--output-dir",required=True)
    args=p.parse_args(); out=Path(args.output_dir); out.mkdir(parents=True,exist_ok=True)
    raw=SOURCE.read_bytes()
    if sha(raw)!=BASE_SHA: raise RuntimeError(f"baseline SHA mismatch: {sha(raw)}")
    text=raw.decode();
    if len(text.splitlines())!=BASE_LINES: raise RuntimeError("baseline line count mismatch")
    seq=[m.group(1) for m in DECL_RE.finditer(text)]
    headers={n:header(text,n) for n in PROTECTED}
    cand=text; repairs=[]
    if args.variant!="baseline":
        cand,rs=apply_gl_pair_cumulative(cand); repairs+=rs
    if args.variant in {"gl_algA","gl_algB","gl_cluster1A","gl_cluster1B"}:
        cand,rs=apply_algebra(cand,"B" if args.variant.endswith("B") else "A"); repairs+=rs
    if args.variant.startswith("gl_cluster1"):
        cand,rs=apply_cluster1(cand); repairs+=rs
    cseq=[m.group(1) for m in DECL_RE.finditer(cand)]
    if cseq!=seq: raise RuntimeError("declaration sequence changed")
    for n,h in headers.items():
        if header(cand,n)!=h: raise RuntimeError(f"theorem/declaration proposition changed: {n}")
    SOURCE.write_text(cand,encoding="utf-8"); data=SOURCE.read_bytes()
    meta={
        "variant":args.variant,"strategy":"gl_analytic_cluster1",
        "baseline_sha256":BASE_SHA,"candidate_sha256":sha(data),
        "line_count":len(cand.splitlines()),"baseline_line_count":BASE_LINES,
        "target_declaration":"actualEdgeAmbientParam_hasDerivAt",
        "target_header_sha256":sha(headers["actualEdgeAmbientParam_hasDerivAt"].encode()),
        "declaration_sequence_sha256":sha(json.dumps(cseq,separators=(",", ":")).encode()),
        "declaration_count":len(cseq),"repairs":repairs,
    }
    (out/"CANDIDATE.json").write_text(json.dumps(meta,indent=2,ensure_ascii=False)+"\n")
    (out/"Mock2_FunctionalAnalysis-candidate.lean").write_bytes(data)
    print(json.dumps(meta,indent=2,ensure_ascii=False))

if __name__=="__main__": main()
