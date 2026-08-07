#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass341_frontier.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/diagnose_pass341_frontier.sh').read_text(encoding='utf-8')


def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


repl(
    "EVIDENCE='/tmp/diagnose-pass341-frontier'",
    "EVIDENCE='/tmp/diagnose-pass342-frontier-v2'",
    'evidence dir',
)
repl(
    "EXPECTED_SHA256='d9bce9ec296c799fe144786111da5a6e8f7f0232f55fd34df9cf09be8b140b4e'",
    "EXPECTED_SHA256='c562c864be74e94e618ad3ad54dd7ee6442f81d17bc748754782718f4f7ca0e0'",
    'expected source hash',
)
repl(
    "  fa340_repair.py \\\n  fa341_repair.py; do",
    "  fa340_repair.py \\\n  fa341_repair.py \\\n  fa342_repair.py; do",
    'PASS342 repair-chain insertion',
)
repl(
    'Mock2_FunctionalAnalysis-pass341-frontier.lean',
    'Mock2_FunctionalAnalysis-pass342-frontier-v2.lean',
    'candidate source name',
)
repl(
    'Mock2_FunctionalAnalysis-pass341-frontier.log',
    'Mock2_FunctionalAnalysis-pass342-frontier-v2.log',
    'candidate log name',
    expected=6,
)
Path('/tmp/diagnose_pass342_frontier_v2.generated.sh').write_text(
    source, encoding='utf-8'
)
PY
bash -n /tmp/diagnose_pass342_frontier_v2.generated.sh
exec bash /tmp/diagnose_pass342_frontier_v2.generated.sh
