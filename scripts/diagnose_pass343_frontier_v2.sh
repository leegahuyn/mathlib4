#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass342_frontier_v2.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path

source = Path('scripts/diagnose_pass342_frontier_v2.sh').read_text(encoding='utf-8')


def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


repl(
    "EVIDENCE='/tmp/diagnose-pass342-frontier-v2'",
    "EVIDENCE='/tmp/diagnose-pass343-frontier-v2'",
    'evidence directory',
)
repl(
    "EXPECTED_SHA256='c562c864be74e94e618ad3ad54dd7ee6442f81d17bc748754782718f4f7ca0e0'",
    "EXPECTED_SHA256='828670615f4d1fdbfb8b84240419f8a745af049729d3f30ebacfefa332d3ba2b'",
    'PASS 343 v2 output hash',
)
repl(
    '  fa342_repair.py; do',
    '  fa342_repair_v2.py \\\n  fa343_frontier_v2_repair.py; do',
    'PASS 342 hash pin plus PASS 343 v2 chain',
)
repl(
    '/tmp/diagnose-pass342-current-advanced.lean',
    '/tmp/diagnose-pass343-v2-current-advanced.lean',
    'Advanced temporary source',
    expected=2,
)
repl(
    'Mock2_FunctionalAnalysis-pass342-frontier-v2.lean',
    'Mock2_FunctionalAnalysis-pass343-frontier-v2.lean',
    'candidate source name',
)
repl(
    'Mock2_FunctionalAnalysis-pass342-frontier-v2.log',
    'Mock2_FunctionalAnalysis-pass343-frontier-v2.log',
    'candidate log name',
    expected=6,
)

out = Path('/tmp/diagnose_pass343_frontier_v2.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY
bash -n /tmp/diagnose_pass343_frontier_v2.generated.sh
exec bash /tmp/diagnose_pass343_frontier_v2.generated.sh
