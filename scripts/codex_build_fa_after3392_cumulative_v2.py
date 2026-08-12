from pathlib import Path

src = Path('scripts/codex_fa_after3392_closed_kernels_v1.sh').read_text()
src = src.replace('codex-fa-after3392-closed-kernels-v1', 'codex-fa-after3392-cumulative-v2')
marker = 'curl --retry 5 --retry-all-errors --fail --silent --show-error https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan.sh'
assert src.count(marker) == 1
extra = '''python3 scripts/codex_fa_apply_weak_smooth_3408_3418.py "$OUT"
python3 scripts/codex_fa_apply_joint_withlp_3432.py "$OUT"

'''
src = src.replace(marker, extra + marker, 1)
Path('/tmp/codex_fa_after3392_cumulative_v2.sh').write_text(src)
