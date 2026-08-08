#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass358_fa.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/diagnose_pass358_fa.sh').read_text(encoding='utf-8')


def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


repl("EVIDENCE='/tmp/diagnose-pass358-fa'", "EVIDENCE='/tmp/diagnose-pass359-fa'", 'evidence dir')
repl(
    '  apply_three_hundred_fifty_eighth_pass_functional_analysis_repairs.py; do',
    '  apply_three_hundred_fifty_eighth_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_fifty_ninth_pass_functional_analysis_repairs.py; do',
    'pass359 chain',
)
repl('Mock2_FunctionalAnalysis-pass358.lean', 'Mock2_FunctionalAnalysis-pass359.lean', 'source name')
repl('Mock2_FunctionalAnalysis-pass358.log', 'Mock2_FunctionalAnalysis-pass359.log', 'log name')
Path('/tmp/diagnose_pass359_fa.generated.sh').write_text(source, encoding='utf-8')
PY
bash -n /tmp/diagnose_pass359_fa.generated.sh
exec bash /tmp/diagnose_pass359_fa.generated.sh
