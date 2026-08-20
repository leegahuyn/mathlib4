from pathlib import Path
src = Path('scripts/codex_fa_after3455_chart_sum_coe_v1.sh').read_text()
src = src.replace('codex-fa-after3455-chart-sum-coe-v1', 'codex-fa-after3455-chart-sum-diagnostic-v2')
old = 'one Mock2_FunctionalAnalysis 1'
new = 'one Mock2_FunctionalAnalysis 20'
assert src.count(old) == 1
src = src.replace(old, new, 1)
Path('/tmp/codex_fa_after3455_chart_sum_diagnostic_v2.sh').write_text(src)
