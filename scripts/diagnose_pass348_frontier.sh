#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass347_frontier.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path

source = Path('scripts/diagnose_pass347_frontier.sh').read_text(encoding='utf-8')


def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


repl(
    "EVIDENCE='/tmp/diagnose-pass347-frontier'",
    "EVIDENCE='/tmp/diagnose-pass348-frontier'",
    'evidence directory',
)
repl(
    "EXPECTED_SHA256='c980501c4a7f0f6582c5d67ec7fa08c7af37ffd6aa3335a3724928f94c2de03f'",
    "EXPECTED_SHA256='2c4376b7b6adaabe7917bbfbc327c622da252a585835461881a9e3ac336dc607'",
    'PASS 348 output hash',
)
new_chain = (
    '  fa347_frontier_repair.py ' + chr(92) + '\n' +
    '  fa348_coherent_frontier_repair.py; do'
)
repl(
    '  fa347_frontier_repair.py; do',
    new_chain,
    'PASS 348 chain',
)
repl(
    '/tmp/diagnose-pass347-current-advanced.lean',
    '/tmp/diagnose-pass348-current-advanced.lean',
    'Advanced temporary source',
    expected=2,
)
repl(
    'Mock2_FunctionalAnalysis-pass347-frontier.lean',
    'Mock2_FunctionalAnalysis-pass348-frontier.lean',
    'candidate source name',
)
repl(
    'Mock2_FunctionalAnalysis-pass347-frontier.log',
    'Mock2_FunctionalAnalysis-pass348-frontier.log',
    'candidate log name',
    expected=6,
)
repl(
    'lake env lean -DmaxErrors=50',
    'lake env lean -DmaxErrors=100',
    'expanded error frontier',
)

out = Path('/tmp/diagnose_pass348_frontier.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY
bash -n /tmp/diagnose_pass348_frontier.generated.sh
exec bash /tmp/diagnose_pass348_frontier.generated.sh
