from pathlib import Path
src = Path('scripts/codex_fa_after3460_friedrichs_real_lsmul_v1.sh').read_text()
src = src.replace('codex-fa-after3460-friedrichs-real-lsmul-v1', 'codex-fa-after3460-friedrichs-diagnostic-v2')
old = 'one Mock2_FunctionalAnalysis 1'
new = 'one Mock2_FunctionalAnalysis 20'
assert src.count(old) == 1
src = src.replace(old, new, 1)
Path('/tmp/codex_fa_after3460_friedrichs_diagnostic_v2.sh').write_text(src)
