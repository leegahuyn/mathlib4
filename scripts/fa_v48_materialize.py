#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path

BASE_SHA = '59418cb02324f5644a52c5a2d1e43820949953736b830a3f955bdc0087c395fc'
BASE_BYTES = 2796085
BASE_LINES = 62559
BASE_DECLS = 4416
TRUST = ('sorry', 'admit', 'axiom', 'unsafe', 'native_decide', 'Lean.ofReduceBool')
DECL_RE = re.compile(r'(?m)^(?:protected\s+|private\s+|noncomputable\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)')

def strip_noncode(text: str) -> str:
    out = list(text); i = 0; depth = 0; string = False; esc = False
    while i < len(out):
        if depth:
            if text.startswith('/-', i): out[i] = out[i+1] = ' '; depth += 1; i += 2; continue
            if text.startswith('-/', i): out[i] = out[i+1] = ' '; depth -= 1; i += 2; continue
            if out[i] != '\n': out[i] = ' '
            i += 1; continue
        if string:
            ch = out[i]
            if ch != '\n': out[i] = ' '
            if esc: esc = False
            elif ch == '\\': esc = True
            elif ch == '"': string = False
            i += 1; continue
        if text.startswith('/-', i): out[i] = out[i+1] = ' '; depth = 1; i += 2; continue
        if text.startswith('--', i):
            while i < len(out) and out[i] != '\n': out[i] = ' '; i += 1
            continue
        if out[i] == '"': out[i] = ' '; string = True
        i += 1
    return ''.join(out)

def trust(text: str) -> dict[str, int]:
    code = strip_noncode(text)
    return {t: len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(t) + r'(?![A-Za-z0-9_])', code)) for t in TRUST}

PATCHES: dict[str, tuple[str, str]] = {
'frontier_ut': (
'''      simpa only [productL1, C, DomAddAct.norm_vadd_Lp] using h''',
'''      simpa only [productL1, C, ut, DomAddAct.norm_vadd_Lp] using h'''),
'plane_coord_simp': (
'''      rw [Fin.prod_univ_two]
      ring_nf
    _ = ((literalStageFourierScale Y)⁻¹ : ℂ) *
          star (UnitAddTorus.mFourier k''',
'''      rw [Fin.prod_univ_two]
      simp
    _ = ((literalStageFourierScale Y)⁻¹ : ℂ) *
          star (UnitAddTorus.mFourier k'''),
'norm_base_ring': (
'''    push_cast
    ring_nf
  have hsum :''',
'''    push_cast
    ring
  have hsum :'''),
'norm_re_inner': (
'''      _ = literalStageFourierScale Y ^ 2 *
          ‖P5LocalFourierRellich.twoTorusFiniteFourierProjection s T - T‖ ^ 2 := by
        rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]''',
'''      _ = literalStageFourierScale Y ^ 2 *
          ‖P5LocalFourierRellich.twoTorusFiniteFourierProjection s T - T‖ ^ 2 := by
        congr 1
        exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm'''),
'ambient_upper_change': (
'''            filter_upwards [MemLp.coeFn_toLp
              (ambientPlane_comp_upper_memLp F)] with z hz
            rw [hz]''',
'''            filter_upwards [MemLp.coeFn_toLp
              (ambientPlane_comp_upper_memLp F)] with z hz
            change ‖((ambientPlane_comp_upper_memLp F).toLp
              (fun z : ℍ ↦ F (z : ℂ)) z)‖ ^ 2 = ‖F (z : ℂ)‖ ^ 2
            rw [hz]'''),
'ambient_stage_change': (
'''  simp only [ambientPlaneToLiteralStage, ContinuousLinearMap.comp_apply]
  rw [hgraph, hstage, hcarrier, hupper,
    completedLiteralStagePlaneBase_core,''',
'''  simp only [ambientPlaneToLiteralStage, ContinuousLinearMap.comp_apply]
  rw [hgraph, hstage, hcarrier]
  change ((ambientPlane_comp_upper_memLp
      (completedLiteralStagePlaneBase Y n (coreMap n u))).toLp
        (fun z : ℍ ↦ completedLiteralStagePlaneBase Y n (coreMap n u) (z : ℂ))) z = _
  rw [hupper,
    completedLiteralStagePlaneBase_core,'''),
'weighted_rfl': (
'''      rw [hv, hmul]
      simp only [Pi.smul_apply, hw, hu]
      rfl''',
'''      rw [hv, hmul]
      rfl'''),
'adjoint_rebundle': (
'''  rw [HalfWeightCompactCoordinateGreen.dx_conjugate_apply,
    HalfWeightCompactCoordinateGreen.dy_conjugate_apply,
    HalfWeightCompactCoordinateGreen.conjugate_apply]
  unfold reducedChartAmbientTest fullPlaneTestToAmbientTestCore
  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
    HalfWeightCompactCoordinateGreen.dy_apply, sub_eq_add_neg,
    star_add, star_mul, star_neg, Complex.conj_I,
    Complex.conj_ofReal, smul_eq_mul]
  ring_nf''',
'''  rw [HalfWeightCompactCoordinateGreen.dx_conjugate_apply,
    HalfWeightCompactCoordinateGreen.dy_conjugate_apply,
    HalfWeightCompactCoordinateGreen.conjugate_apply]
  have hfun : (reducedChartAmbientTest v hv : ℂ → ℂ) = (v : ℂ → ℂ) := by
    funext z
    exact reducedChartAmbientTest_apply v hv z
  rw [hfun]
  simp only [HalfWeightCompactCoordinateGreen.dx_apply,
    HalfWeightCompactCoordinateGreen.dy_apply, sub_eq_add_neg,
    star_add, star_mul, star_neg, Complex.conj_I,
    Complex.conj_ofReal, smul_eq_mul]
  ring_nf'''),
'dxdy_function_eq': (
'''  have hRight : Integrable
      (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) 1)
      (volume : Measure ℂ) := by
    simpa only [HalfWeightCompactCoordinateGreen.dx_apply] using
      ((literalStageNegativePlaneWave_continuous Y k).mul
        (HalfWeightCompactCoordinateGreen.dx v).continuous).integrable_of_hasCompactSupport
          (HalfWeightCompactCoordinateGreen.dx v).hasCompactSupport.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (v := (1 : ℂ))
    hLeft hRight hBase
    (fun _ _ ↦
      (literalStageNegativePlaneWave_differentiable Y k).differentiableAt)
    (fun _ _ ↦ v.contDiff.differentiable (by simp) _)
  rw [HalfWeightCompactCoordinateGreen.dx_apply]''',
'''  have hdx : (HalfWeightCompactCoordinateGreen.dx v : ℂ → ℂ) =
      fun w : ℂ ↦ (fderiv ℝ (v : ℂ → ℂ) w) 1 := by
    funext w
    exact HalfWeightCompactCoordinateGreen.dx_apply v w
  have hRight : Integrable
      (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) 1)
      (volume : Measure ℂ) := by
    rw [← hdx]
    exact ((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dx v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dx v).hasCompactSupport.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (v := (1 : ℂ))
    hLeft hRight hBase
    (fun _ _ ↦
      (literalStageNegativePlaneWave_differentiable Y k).differentiableAt)
    (fun _ _ ↦ v.contDiff.differentiable (by simp) _)
  rw [hdx]'''),
'dy_function_eq': (
'''  have hRight : Integrable
      (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) Complex.I)
      (volume : Measure ℂ) := by
    simpa only [HalfWeightCompactCoordinateGreen.dy_apply] using
      ((literalStageNegativePlaneWave_continuous Y k).mul
        (HalfWeightCompactCoordinateGreen.dy v).continuous).integrable_of_hasCompactSupport
          (HalfWeightCompactCoordinateGreen.dy v).hasCompactSupport.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ))
    (f := literalStageNegativePlaneWave Y k) (g := (v : ℂ → ℂ))
    (v := Complex.I)
    hLeft hRight hBase
    (fun _ _ ↦
      (literalStageNegativePlaneWave_differentiable Y k).differentiableAt)
    (fun _ _ ↦ v.contDiff.differentiable (by simp) _)
  rw [HalfWeightCompactCoordinateGreen.dy_apply]''',
'''  have hdy : (HalfWeightCompactCoordinateGreen.dy v : ℂ → ℂ) =
      fun w : ℂ ↦ (fderiv ℝ (v : ℂ → ℂ) w) Complex.I := by
    funext w
    exact HalfWeightCompactCoordinateGreen.dy_apply v w
  have hRight : Integrable
      (fun w : ℂ ↦ literalStageNegativePlaneWave Y k w *
        (fderiv ℝ (v : ℂ → ℂ) w) Complex.I)
      (volume : Measure ℂ) := by
    rw [← hdy]
    exact ((literalStageNegativePlaneWave_continuous Y k).mul
      (HalfWeightCompactCoordinateGreen.dy v).continuous).integrable_of_hasCompactSupport
        (HalfWeightCompactCoordinateGreen.dy v).hasCompactSupport.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ))
    (f := literalStageNegativePlaneWave Y k) (g := (v : ℂ → ℂ))
    (v := Complex.I)
    hLeft hRight hBase
    (fun _ _ ↦
      (literalStageNegativePlaneWave_differentiable Y k).differentiableAt)
    (fun _ _ ↦ v.contDiff.differentiable (by simp) _)
  rw [hdy]'''),
'deriv_simp': (
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>
    try simp only [one_div, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_one, add_zero, zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring''',
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>
    try with_reducible rfl <;>
    simp [id, one_div, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc,
      Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring'''),
'deriv_simp_I': (
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>
    try simp only [one_div, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.real_smul, smul_eq_mul, mul_one, add_zero,
      zero_mul, Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring''',
'''      ((literalStageFourierScale Y)⁻¹ : ℂ) using 1 <;>
    try with_reducible rfl <;>
    simp [id, one_div, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc,
      Complex.ofReal_inv, Complex.ofReal_mul] <;>
    field_simp [literalStageFourierScale_ne_zero Y] <;> ring'''),
'torus_coeff_normalize': (
'''  rw [UnitAddTorus.integral_preimage
    (fun t : P5LocalFourierRellich.TwoTorus ↦
      UnitAddTorus.mFourier (-k) t *
        literalStageTorusRepresentative Y v t)
    (fun _ : Fin 2 ↦ -(1 / 2 : ℝ))]
  rw [← literalStageFourierBox_eq_smul_unitPiBox Y,''',
'''  rw [UnitAddTorus.integral_preimage
    (fun t : P5LocalFourierRellich.TwoTorus ↦
      UnitAddTorus.mFourier (-k) t *
        literalStageTorusRepresentative Y v t)
    (fun _ : Fin 2 ↦ -(1 / 2 : ℝ))]
  have hhalf : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [hhalf]
  rw [← literalStageFourierBox_eq_smul_unitPiBox Y,'''),
'torus_inner_reorder': (
'''      rw [← literalStageFourierBox_eq_smul_unitPiBox Y,
        Measure.setIntegral_comp_smul_of_pos volume
          (fun w : ℂ ↦
            inner ℂ (literalStagePlaneWave Y k w)
              (literalStagePlaneWave Y l w))
          (Complex.measurableEquivPi.symm '' literalStageUnitPiBox)
          (literalStageFourierScale_pos Y)]
      rw [UnitAddTorus.integral_preimage
        (fun t : P5LocalFourierRellich.TwoTorus ↦
          inner ℂ (UnitAddTorus.mFourier k t)
            (UnitAddTorus.mFourier l t))
        (fun _ : Fin 2 ↦ -(1 / 2 : ℝ))]''',
'''      rw [UnitAddTorus.integral_preimage
        (fun t : P5LocalFourierRellich.TwoTorus ↦
          inner ℂ (UnitAddTorus.mFourier k t)
            (UnitAddTorus.mFourier l t))
        (fun _ : Fin 2 ↦ -(1 / 2 : ℝ))]
      have hhalf : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
      rw [hhalf]
      rw [← literalStageFourierBox_eq_smul_unitPiBox Y,
        Measure.setIntegral_comp_smul_of_pos volume
          (fun w : ℂ ↦
            inner ℂ (literalStagePlaneWave Y k w)
              (literalStagePlaneWave Y l w))
          (Complex.measurableEquivPi.symm '' literalStageUnitPiBox)
          (literalStageFourierScale_pos Y)]'''),
}

CORE = [
    'frontier_ut', 'plane_coord_simp', 'norm_base_ring', 'norm_re_inner',
    'ambient_upper_change', 'ambient_stage_change', 'weighted_rfl',
    'adjoint_rebundle',
]
VARIANTS = {
    'core': CORE,
    'core_dxdy': CORE + ['dxdy_function_eq', 'dy_function_eq'],
    'core_deriv': CORE + ['deriv_simp', 'deriv_simp_I'],
    'core_torus': CORE + ['torus_coeff_normalize', 'torus_inner_reorder'],
    'core_dxdy_deriv': CORE + ['dxdy_function_eq', 'dy_function_eq', 'deriv_simp', 'deriv_simp_I'],
    'max_batch': CORE + ['dxdy_function_eq', 'dy_function_eq', 'deriv_simp', 'deriv_simp_I',
                          'torus_coeff_normalize', 'torus_inner_reorder'],
}

def apply_one(text: str, name: str) -> str:
    old, new = PATCHES[name]
    count = text.count(old)
    expected = 2 if name == 'adjoint_rebundle' else 1
    if count != expected:
        raise RuntimeError(f'{name}: expected {expected} old block(s), got {count}')
    return text.replace(old, new, expected)

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', type=Path, required=True)
    ap.add_argument('--variant', choices=VARIANTS, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--audit', type=Path, required=True)
    a = ap.parse_args()
    raw = a.base.read_bytes(); text = raw.decode()
    assert hashlib.sha256(raw).hexdigest() == BASE_SHA
    assert len(raw) == BASE_BYTES and len(text.splitlines()) == BASE_LINES
    before_decls = DECL_RE.findall(text); assert len(before_decls) == BASE_DECLS
    before_trust = trust(text); assert all(v == 0 for v in before_trust.values())
    applied: list[str] = []
    for name in VARIANTS[a.variant]:
        text = apply_one(text, name); applied.append(name)
    after_decls = DECL_RE.findall(text); after_trust = trust(text)
    assert after_decls == before_decls
    assert all(v == 0 for v in after_trust.values())
    data = text.encode(); a.out.parent.mkdir(parents=True, exist_ok=True); a.out.write_bytes(data)
    audit = {
        'schema': 'fa-v48-materialization-audit-v1', 'variant': a.variant,
        'base_sha256': BASE_SHA, 'base_bytes': BASE_BYTES, 'base_lines': BASE_LINES,
        'base_declarations': BASE_DECLS,
        'source_sha256': hashlib.sha256(data).hexdigest(), 'source_bytes': len(data),
        'source_lines': len(text.splitlines()), 'source_declarations': len(after_decls),
        'declaration_sequence_identical': after_decls == before_decls,
        'trust_before': before_trust, 'trust_after': after_trust,
        'applied_patches': applied, 'public_header_changes': False,
        'comments_changed': False, 'attributes_changed': False,
    }
    a.audit.parent.mkdir(parents=True, exist_ok=True)
    a.audit.write_text(json.dumps(audit, indent=2, sort_keys=True) + '\n')
    print(json.dumps(audit, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
