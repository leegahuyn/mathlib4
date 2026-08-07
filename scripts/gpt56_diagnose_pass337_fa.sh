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
    "EVIDENCE='/tmp/gpt56-focused-pass337-fa'",
    'focused PASS 337 evidence directory',
)
replace_exact(
    "EXPECTED_SHA256='f39bad641a544d23c59871b91d3e3eb677cf8fca25e0bf49c10d28d48503b576'",
    "EXPECTED_SHA256='a1019626213bcd9792a1d6f8a19412b9d85d14ff94a2994b444d194e1c8d6128'",
    'focused PASS 337 expected hash',
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
  apply_three_hundred_thirty_seventh_pass_functional_analysis_repairs.py; do''',
    'focused PASS 329-337 chain',
)
replace_exact(
    'Mock2_FunctionalAnalysis-pass328.lean',
    'Mock2_FunctionalAnalysis-pass337.lean',
    'focused PASS 337 source name',
)
replace_exact(
    'Mock2_FunctionalAnalysis-pass328.log',
    'Mock2_FunctionalAnalysis-pass337.log',
    'focused PASS 337 log name',
    expected=6,
)

out = Path('/tmp/gpt56_diagnose_pass337_fa.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY

bash -n /tmp/gpt56_diagnose_pass337_fa.generated.sh
exec bash /tmp/gpt56_diagnose_pass337_fa.generated.sh
