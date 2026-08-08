#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass360_fa.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/diagnose_pass360_fa.sh').read_text(encoding='utf-8')


def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


repl("EVIDENCE='/tmp/diagnose-pass360-fa'", "EVIDENCE='/tmp/diagnose-pass361r2-fa'", 'evidence dir')
repl(
    '  apply_three_hundred_sixtieth_pass_functional_analysis_repairs.py; do',
    '  apply_three_hundred_sixtieth_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_sixty_first_pass_functional_analysis_repairs.py; do',
    'pass361 chain',
)
repl('Mock2_FunctionalAnalysis-pass360.lean', 'Mock2_FunctionalAnalysis-pass361r2.lean', 'source name')
repl('Mock2_FunctionalAnalysis-pass360.log', 'Mock2_FunctionalAnalysis-pass361r2.log', 'log name')
Path('/tmp/diagnose_pass361r2_fa.generated.sh').write_text(source, encoding='utf-8')
PY
bash -n /tmp/diagnose_pass361r2_fa.generated.sh
exec bash /tmp/diagnose_pass361r2_fa.generated.sh
