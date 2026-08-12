from pathlib import Path

src = Path('scripts/codex_fa_after3455_clm_sum_v1.sh').read_text()
src = src.replace('codex-fa-after3455-clm-sum-v1', 'codex-fa-after3455-plus-3460-3467-v1')
src = src.replace("'schema':'fa-after3455-clm-sum-v1'", "'schema':'fa-after3455-plus-3460-3467-v1'")
marker = "after=before.replace(old,new,1)\np.write_text(after)"
insert = r'''after=before.replace(old,new,1)
old3460='''  have hDerivative :=
    (friedrichsMollifierReal_hasCompactSupport j).hasFDerivAt_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℂ) hRhoOne hLocal w
  rw [hDerivative.fderiv]
  have hDerivativeConvolution : ConvolutionExists
      (fderiv ℝ (friedrichsMollifierReal j)) (u : ℂ → ℂ)
      ((ContinuousLinearMap.lsmul ℝ ℂ).precompL ℂ) (volume : Measure ℂ) :=
    ((friedrichsMollifierReal_hasCompactSupport j).fderiv ℝ).convolutionExists_left
        ((ContinuousLinearMap.lsmul ℝ ℂ).precompL ℂ)
        hRhoOne.continuous_fderiv (by norm_num) hLocal'''
new3460='''  have hDerivative :=
    (friedrichsMollifierReal_hasCompactSupport j).hasFDerivAt_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) hRhoOne hLocal w
  rw [hDerivative.fderiv]
  have hDerivativeConvolution : ConvolutionExists
      (fderiv ℝ (friedrichsMollifierReal j)) (u : ℂ → ℂ)
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).precompL ℂ)
        (volume : Measure ℂ) :=
    ((friedrichsMollifierReal_hasCompactSupport j).fderiv ℝ).convolutionExists_left
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).precompL ℂ)
        hRhoOne.continuous_fderiv (by norm_num) hLocal'''
assert after.count(old3460)==1, after.count(old3460)
after=after.replace(old3460,new3460,1)
old3467='''    Complex.sub_im]
  ring'''
new3467='''    Complex.sub_im]
  push_cast
  ring'''
assert after.count(old3467)==1, after.count(old3467)
after=after.replace(old3467,new3467,1)
p.write_text(after)'''
assert src.count(marker) == 1, src.count(marker)
src = src.replace(marker, insert, 1)
Path('/tmp/codex_fa_after3455_plus_3460_3467_v1.sh').write_text(src)
