#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass328_fa.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/diagnose_pass328_fa.sh').read_text(encoding='utf-8')

def repl(old: str, new: str, label: str) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected=1 actual={count}')
    if count != 1:
        raise SystemExit(f'{label}: expected one occurrence, found {count}')
    source = source.replace(old, new)

repl("EVIDENCE='/tmp/diagnose-pass328-fa'", "EVIDENCE='/tmp/diagnose-pass329-fa'", 'evidence dir')
repl(
    "EXPECTED_SHA256='f39bad641a544d23c59871b91d3e3eb677cf8fca25e0bf49c10d28d48503b576'",
    "EXPECTED_SHA256='d38f2f58649a4acda650c92d4a36a6df063b86dbe144ce958dc1c1a096168189'",
    'expected hash',
)
repl(
    "  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py; do",
    "  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_twenty_ninth_pass_functional_analysis_repairs.py; do",
    'pass329 chain',
)
repl('Mock2_FunctionalAnalysis-pass328.lean', 'Mock2_FunctionalAnalysis-pass329.lean', 'source name')
repl('Mock2_FunctionalAnalysis-pass328.log', 'Mock2_FunctionalAnalysis-pass329.log', 'log name occurrences')
Path('/tmp/diagnose_pass329_fa.generated.sh').write_text(source, encoding='utf-8')
PY
bash -n /tmp/diagnose_pass329_fa.generated.sh
exec bash /tmp/diagnose_pass329_fa.generated.sh
