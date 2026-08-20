from pathlib import Path
import subprocess

# First build the exact broad-simp carrier candidate from the authoritative idx3392 artifact.
subprocess.run(['python3', 'scripts/codex_build_fa_after3392_closed_kernels_v2.py'], check=True)
p = Path('/tmp/codex_fa_after3392_closed_kernels_v2.sh')
src = p.read_text()
src = src.replace('codex-fa-after3392-closed-kernels-v2', 'codex-fa-after3392-closed-kernels-cumulative-v3')
marker = 'curl --retry 5 --retry-all-errors --fail --silent --show-error https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan.sh'
assert src.count(marker) == 1
extra = (
    'python3 scripts/codex_fa_apply_weak_downstream_3392_3407.py "$OUT"\n'
    'python3 scripts/codex_fa_apply_weak_smooth_3408_3418.py "$OUT"\n'
    'python3 scripts/codex_fa_apply_joint_withlp_3432.py "$OUT"\n\n'
)
src = src.replace(marker, extra + marker, 1)
Path('/tmp/codex_fa_after3392_closed_kernels_cumulative_v3.sh').write_text(src)
