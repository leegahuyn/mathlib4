#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass328_fa.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/diagnose_pass328_fa.sh').read_text(encoding='utf-8')

def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)

repl("EVIDENCE='/tmp/diagnose-pass328-fa'", "EVIDENCE='/tmp/diagnose-pass332-fa'", 'evidence dir')
repl(
    "EXPECTED_SHA256='f39bad641a544d23c59871b91d3e3eb677cf8fca25e0bf49c10d28d48503b576'",
    "EXPECTED_SHA256='9377a1c2b13cae183c95e3006b8974e6e1e6772471cbe269a6bb8dd7f3b367c1'",
    'expected hash',
)
repl(
    "  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py; do",
    "  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_twenty_ninth_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_thirtieth_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_thirty_first_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_thirty_second_pass_functional_analysis_repairs.py; do",
    'pass332 chain',
)
repl('Mock2_FunctionalAnalysis-pass328.lean', 'Mock2_FunctionalAnalysis-pass332.lean', 'source name')
repl(
    'Mock2_FunctionalAnalysis-pass328.log',
    'Mock2_FunctionalAnalysis-pass332.log',
    'log name',
    expected=6,
)
Path('/tmp/diagnose_pass332_fa.generated.sh').write_text(source, encoding='utf-8')
PY
bash -n /tmp/diagnose_pass332_fa.generated.sh
exec bash /tmp/diagnose_pass332_fa.generated.sh
