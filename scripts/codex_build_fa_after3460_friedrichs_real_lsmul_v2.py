from pathlib import Path
src = Path('scripts/codex_fa_after3460_friedrichs_real_lsmul_v1.sh').read_text()
src = src.replace('codex-fa-after3460-friedrichs-real-lsmul-v1', 'codex-fa-after3460-friedrichs-real-lsmul-v2')
src = src.replace("assert block.count(old)==2, block.count(old)", "assert block.count(old)==3, block.count(old)")
src = src.replace("newblock=block.replace(old,'ContinuousLinearMap.lsmul ℝ ℝ')", "newblock=block.replace(old,'(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)')")
src = src.replace("'replacements':2", "'replacements':3")
src = src.replace("'schema':'fa-after3460-friedrichs-real-lsmul-v1'", "'schema':'fa-after3460-friedrichs-real-lsmul-v2'")
Path('/tmp/codex_fa_after3460_friedrichs_real_lsmul_v2.sh').write_text(src)
