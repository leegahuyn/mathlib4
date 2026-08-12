from pathlib import Path
src = Path('scripts/codex_fa_after3392_closed_kernels_v1.sh').read_text()
src = src.replace('codex-fa-after3392-closed-kernels-v1', 'codex-fa-after3392-cumulative-v3')
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
src = src.replace(old_r,new_r,1)
assert src.count(old_l) == 1
src = src.replace(old_l,new_l,1)
marker = 'curl --retry 5 --retry-all-errors --fail --silent --show-error https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan.sh'
assert src.count(marker) == 1
extra = '''python3 scripts/codex_fa_apply_weak_smooth_3408_3418.py "$OUT"
python3 scripts/codex_fa_apply_joint_withlp_3432.py "$OUT"

'''
src = src.replace(marker,extra+marker,1)
Path('/tmp/codex_fa_after3392_cumulative_v3.sh').write_text(src)
