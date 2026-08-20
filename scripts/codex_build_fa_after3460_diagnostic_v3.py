from pathlib import Path
import subprocess
subprocess.run(['python3','scripts/codex_build_fa_after3460_friedrichs_real_lsmul_v2.py'], check=True)
src = Path('/tmp/codex_fa_after3460_friedrichs_real_lsmul_v2.sh').read_text()
src = src.replace('codex-fa-after3460-friedrichs-real-lsmul-v2', 'codex-fa-after3460-friedrichs-diagnostic-v3')
old = 'one Mock2_FunctionalAnalysis 1'
new = 'one Mock2_FunctionalAnalysis 20'
assert src.count(old) == 1
src = src.replace(old, new, 1)
Path('/tmp/codex_fa_after3460_friedrichs_diagnostic_v3.sh').write_text(src)
