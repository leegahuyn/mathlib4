from pathlib import Path
src = Path('scripts/codex_fa_after3392_closed_kernels_v1.sh').read_text()
src = src.replace('codex-fa-after3392-closed-kernels-v1', 'codex-fa-after3392-closed-kernels-v2')
old_r = '''    ext x
    simpa only [Set.mem_iInter, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] using
        (mem_weakRaisingSubmodule_iff n x)'''
new_r = '''    ext x
    simp [weakRaisingSubmodule]'''
old_l = '''    ext x
    simpa only [Set.mem_iInter, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] using
        (mem_weakLoweringSubmodule_iff n x)'''
new_l = '''    ext x
    simp [weakLoweringSubmodule]'''
assert src.count(old_r) == 1
src = src.replace(old_r, new_r, 1)
assert src.count(old_l) == 1
src = src.replace(old_l, new_l, 1)
Path('/tmp/codex_fa_after3392_closed_kernels_v2.sh').write_text(src)
