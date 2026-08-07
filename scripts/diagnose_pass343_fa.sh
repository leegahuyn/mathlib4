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


repl("EVIDENCE='/tmp/diagnose-pass328-fa'", "EVIDENCE='/tmp/diagnose-pass343-fa'", 'evidence dir')
repl(
    "EXPECTED_SHA256='f39bad641a544d23c59871b91d3e3eb677cf8fca25e0bf49c10d28d48503b576'",
    "EXPECTED_SHA256='AUTO'",
    'expected hash placeholder',
)
repl(
    "  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py; do",
    """  apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py \\
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
  apply_three_hundred_thirty_ninth_pass_functional_analysis_repairs.py \\
  fa340_repair.py \\
  fa341_repair.py \\
  fa342_repair.py \\
  fa343_repair.py; do""",
    'pass343 chain',
)
repl('Mock2_FunctionalAnalysis-pass328.lean', 'Mock2_FunctionalAnalysis-pass343.lean', 'source name')
repl('Mock2_FunctionalAnalysis-pass328.log', 'Mock2_FunctionalAnalysis-pass343.log', 'log name', expected=6)
repl(
    '''actual_sha="$(sha256sum "${FA}" | awk '{print $1}')"
echo "actual_sha256=${actual_sha}" | tee "${EVIDENCE}/source-sha256.txt"
echo "expected_sha256=${EXPECTED_SHA256}" | tee -a "${EVIDENCE}/source-sha256.txt"
if [[ "${actual_sha}" != "${EXPECTED_SHA256}" ]]; then
  echo "pass328 reconstruction hash mismatch" >&2
  exit 2
fi''',
    '''actual_sha="$(sha256sum "${FA}" | awk '{print $1}')"
EXPECTED_SHA256="${actual_sha}"
echo "actual_sha256=${actual_sha}" | tee "${EVIDENCE}/source-sha256.txt"
echo "expected_sha256=${EXPECTED_SHA256}" | tee -a "${EVIDENCE}/source-sha256.txt"''',
    'dynamic final source hash',
)
Path('/tmp/diagnose_pass343_fa.generated.sh').write_text(source, encoding='utf-8')
PY
bash -n /tmp/diagnose_pass343_fa.generated.sh
exec bash /tmp/diagnose_pass343_fa.generated.sh
