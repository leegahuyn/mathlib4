#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/diagnose_pass328_fa.sh'
test -f "${BASE}"

python3 - <<'PY'
from pathlib import Path

source = Path('scripts/diagnose_pass328_fa.sh').read_text(encoding='utf-8')


def replace_exact(old: str, new: str, label: str, expected: int = 1) -> None:
    global source
    count = source.count(old)
    print(f'{label}: expected={expected} actual={count}')
    if count != expected:
        raise SystemExit(f'{label}: expected {expected} occurrence(s), found {count}')
    source = source.replace(old, new)


replace_exact(
    "EVIDENCE='/tmp/diagnose-pass328-fa'",
    "EVIDENCE='/tmp/gpt56-focused-pass339-fa'",
    'focused PASS 339 evidence directory',
)
replace_exact(
    "EXPECTED_SHA256='f39bad641a544d23c59871b91d3e3eb677cf8fca25e0bf49c10d28d48503b576'",
    "EXPECTED_SHA256='11f5d0b53aa640d44169a05d02c0a0cbe90dfe8fa53cab4e4f66131a01a089fd'",
    'focused PASS 339 expected hash',
)
replace_exact(
    '  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py; do',
    '''  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py \\
  apply_three_hundred_twenty_ninth_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirtieth_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirty_first_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirty_second_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirty_third_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirty_fourth_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirty_fifth_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirty_sixth_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirty_seventh_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirty_eighth_pass_functional_analysis_repairs.py \\
  apply_three_hundred_thirty_ninth_pass_functional_analysis_repairs.py; do''',
    'focused PASS 329-339 chain',
)
replace_exact(
    'Mock2_FunctionalAnalysis-pass328.lean',
    'Mock2_FunctionalAnalysis-pass339.lean',
    'focused PASS 339 source name',
)
replace_exact(
    'Mock2_FunctionalAnalysis-pass328.log',
    'Mock2_FunctionalAnalysis-pass339.log',
    'focused PASS 339 log name',
    expected=6,
)

out = Path('/tmp/gpt56_diagnose_pass339_fa.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY

bash -n /tmp/gpt56_diagnose_pass339_fa.generated.sh
exec bash /tmp/gpt56_diagnose_pass339_fa.generated.sh
