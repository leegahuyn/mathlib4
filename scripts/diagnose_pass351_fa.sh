#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass350_fa.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/diagnose_pass350_fa.sh').read_text(encoding='utf-8')


def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


repl("EVIDENCE='/tmp/diagnose-pass350-fa'", "EVIDENCE='/tmp/diagnose-pass351-fa'", 'evidence dir')
repl(
    '  apply_three_hundred_fiftieth_pass_functional_analysis_repairs.py; do',
    '  apply_three_hundred_fiftieth_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_fifty_first_pass_functional_analysis_repairs.py; do',
    'pass351 chain',
)
repl('Mock2_FunctionalAnalysis-pass350.lean', 'Mock2_FunctionalAnalysis-pass351.lean', 'source name')
repl('Mock2_FunctionalAnalysis-pass350.log', 'Mock2_FunctionalAnalysis-pass351.log', 'log name')
Path('/tmp/diagnose_pass351_fa.generated.sh').write_text(source, encoding='utf-8')
PY
bash -n /tmp/diagnose_pass351_fa.generated.sh
exec bash /tmp/diagnose_pass351_fa.generated.sh
