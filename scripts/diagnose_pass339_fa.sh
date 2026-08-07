#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass338_fa.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/diagnose_pass338_fa.sh').read_text(encoding='utf-8')

def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)

repl("EVIDENCE='/tmp/diagnose-pass338-fa'", "EVIDENCE='/tmp/diagnose-pass339-fa'", 'evidence dir')
repl(
    "EXPECTED_SHA256='1d150bcb8bd909e1bde7ce3577cf754386efcd7be2902d68a7c78b72b28d6b39'",
    "EXPECTED_SHA256='6c277b2a7eefc7c4bd776ddd2b37550268a058d333b2457a6b5428d5cf419599'",
    'expected hash',
)
repl(
    "  apply_three_hundred_thirty_eighth_pass_functional_analysis_repairs.py; do",
    "  apply_three_hundred_thirty_eighth_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_thirty_ninth_pass_functional_analysis_repairs.py; do",
    'pass339 chain',
)
repl('Mock2_FunctionalAnalysis-pass338.lean', 'Mock2_FunctionalAnalysis-pass339.lean', 'source name')
repl('Mock2_FunctionalAnalysis-pass338.log', 'Mock2_FunctionalAnalysis-pass339.log', 'log name', expected=6)
Path('/tmp/diagnose_pass339_fa.generated.sh').write_text(source, encoding='utf-8')
PY
bash -n /tmp/diagnose_pass339_fa.generated.sh
exec bash /tmp/diagnose_pass339_fa.generated.sh
