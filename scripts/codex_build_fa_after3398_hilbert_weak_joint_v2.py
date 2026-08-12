from pathlib import Path
src = Path('scripts/codex_fa_after3398_hilbert_witness_v1.sh').read_text()
src = src.replace('codex-fa-after3398-hilbert-witness-v1', 'codex-fa-after3398-hilbert-weak-joint-v2')
marker = 'curl --retry 5 --retry-all-errors --fail --silent --show-error https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan.sh'
assert src.count(marker) == 1
extra = '''python3 scripts/codex_fa_apply_weak_smooth_3408_3418.py "$OUT"
python3 scripts/codex_fa_apply_joint_withlp_3432.py "$OUT"

'''
src = src.replace(marker, extra + marker, 1)
Path('/tmp/codex_fa_after3398_hilbert_weak_joint_v2.sh').write_text(src)
