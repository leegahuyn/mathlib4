#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass344_frontier_v2.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path

source = Path('scripts/diagnose_pass344_frontier_v2.sh').read_text(encoding='utf-8')


def repl(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


repl(
    "EVIDENCE='/tmp/diagnose-pass344-frontier-v2'",
    "EVIDENCE='/tmp/diagnose-pass346-global-frontier'",
    'evidence directory',
)
repl(
    "EXPECTED_SHA256='59d4bcc02ff615190da0691c9bef52fe3d8bfcb0b8cdf573c300e258757376b6'",
    "EXPECTED_SHA256='be21e702089c0de8f9a5a4e5c1af8eb0963869cf93271c469d0516e55caa6fd5'",
    'PASS 346 global output hash',
)
repl(
    '  fa344_frontier_v2_repair.py; do',
    '  fa344_frontier_v2_repair.py \\\n  fa345_global_instances_repair.py \\\n  fa346_global_neg_repair.py; do',
    'PASS 345 and PASS 346 global chain',
)
repl(
    '/tmp/diagnose-pass344-v2-current-advanced.lean',
    '/tmp/diagnose-pass346-global-current-advanced.lean',
    'Advanced temporary source',
)
repl(
    'Mock2_FunctionalAnalysis-pass344-frontier-v2.lean',
    'Mock2_FunctionalAnalysis-pass346-global-frontier.lean',
    'candidate source name',
)
repl(
    'Mock2_FunctionalAnalysis-pass344-frontier-v2.log',
    'Mock2_FunctionalAnalysis-pass346-global-frontier.log',
    'candidate log name',
)

out = Path('/tmp/diagnose_pass346_global_frontier.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY
bash -n /tmp/diagnose_pass346_global_frontier.generated.sh
exec bash /tmp/diagnose_pass346_global_frontier.generated.sh
