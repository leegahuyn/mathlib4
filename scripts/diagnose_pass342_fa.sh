#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass341_fa.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/diagnose_pass341_fa.sh').read_text(encoding='utf-8')

def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)

repl("EVIDENCE='/tmp/diagnose-pass341-fa'", "EVIDENCE='/tmp/diagnose-pass342-fa'", 'evidence dir')
repl(
    '  apply_three_hundred_forty_first_pass_functional_analysis_repairs.py; do',
    '  apply_three_hundred_forty_first_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_forty_second_pass_functional_analysis_repairs.py; do',
    'pass342 chain',
)
repl('Mock2_FunctionalAnalysis-pass341.lean', 'Mock2_FunctionalAnalysis-pass342.lean', 'source name')
repl('Mock2_FunctionalAnalysis-pass341.log', 'Mock2_FunctionalAnalysis-pass342.log', 'log name', expected=6)
Path('/tmp/diagnose_pass342_fa.generated.sh').write_text(source, encoding='utf-8')
PY
bash -n /tmp/diagnose_pass342_fa.generated.sh
exec bash /tmp/diagnose_pass342_fa.generated.sh
