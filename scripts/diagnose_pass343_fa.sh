#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass342_fa.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/diagnose_pass342_fa.sh').read_text(encoding='utf-8')


def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


repl("EVIDENCE='/tmp/diagnose-pass342-fa'", "EVIDENCE='/tmp/diagnose-pass343-fa'", 'evidence dir')
repl(
    '  apply_three_hundred_forty_second_pass_functional_analysis_repairs.py; do',
    '  apply_three_hundred_forty_second_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_forty_third_pass_functional_analysis_repairs.py; do',
    'pass343 chain',
)
repl('Mock2_FunctionalAnalysis-pass342.lean', 'Mock2_FunctionalAnalysis-pass343.lean', 'source name')
repl('Mock2_FunctionalAnalysis-pass342.log', 'Mock2_FunctionalAnalysis-pass343.log', 'log name')
Path('/tmp/diagnose_pass343_fa.generated.sh').write_text(source, encoding='utf-8')
PY
bash -n /tmp/diagnose_pass343_fa.generated.sh
exec bash /tmp/diagnose_pass343_fa.generated.sh
