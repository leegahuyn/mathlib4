#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/gpt56_isolated_pass336_gate.sh'
test -f "${BASE}"

python3 - <<'PY'
from pathlib import Path

source = Path('scripts/gpt56_isolated_pass336_gate.sh').read_text(encoding='utf-8')


def replace_exact(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


replace_exact(
    "EVIDENCE='/tmp/gpt56-pass336-gate'",
    "EVIDENCE='/tmp/gpt56-pass337-gate'",
    'PASS 337 evidence directory',
)
replace_exact(
    "EXPECTED_FA_SHA256='204acd949c17f55013487819b215886ae5c1c5fb4d125d4683871f8fb94847ad'",
    "EXPECTED_FA_SHA256='a1019626213bcd9792a1d6f8a19412b9d85d14ff94a2994b444d194e1c8d6128'",
    'PASS 337 expected source hash',
)
replace_exact(
    '  apply_three_hundred_thirty_sixth_pass_functional_analysis_repairs.py; do',
    '  apply_three_hundred_thirty_sixth_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_thirty_seventh_pass_functional_analysis_repairs.py; do',
    'PASS 337 repair-chain insertion',
)
replace_exact(
    'Mock2_FunctionalAnalysis-pass336.lean',
    'Mock2_FunctionalAnalysis-pass337.lean',
    'PASS 337 candidate source name',
)
replace_exact('FA-pass336-direct-1', 'FA-pass337-direct-1', 'PASS 337 first compile label', expected=2)
replace_exact('FA-pass336-direct-2', 'FA-pass337-direct-2', 'PASS 337 second compile label', expected=2)
replace_exact(
    'FAIL: FunctionalAnalysis PASS 336 direct compile 1',
    'FAIL: FunctionalAnalysis PASS 337 direct compile 1',
    'PASS 337 first failure status',
)
replace_exact(
    'FAIL: FunctionalAnalysis PASS 336 direct compile 2',
    'FAIL: FunctionalAnalysis PASS 337 direct compile 2',
    'PASS 337 second failure status',
)

out = Path('/tmp/gpt56_isolated_pass337_gate.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY

bash -n /tmp/gpt56_isolated_pass337_gate.generated.sh
exec bash /tmp/gpt56_isolated_pass337_gate.generated.sh
