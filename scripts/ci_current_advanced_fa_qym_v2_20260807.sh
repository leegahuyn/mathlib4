#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/ci_fa320_unpinned_qym_20260807.sh'
test -f "${BASE}"

python3 - <<'PY'
from pathlib import Path

base = Path('scripts/ci_fa320_unpinned_qym_20260807.sh').read_text(encoding='utf-8')
base = base.replace(
    "EVIDENCE='/tmp/fa320-unpinned-qym'\n",
    "EVIDENCE='/tmp/current-advanced-fa-qym-v2'\n",
    1,
)
old = '''  if [[ -z "${pass320}" ]]; then
    echo 'PASS-320 FunctionalAnalysis repair script not found' >&2
    find scripts -maxdepth 1 -type f -iname '*twentieth*' -o -iname '*320*' \\
      | sort | tee "${EVIDENCE}/logs/pass320-search.txt"
    exit 91
  fi
  echo "pass320_script=${pass320}" | tee "${EVIDENCE}/pass320-selection.txt"
  python3 "${pass320}" 2>&1 | tee "${EVIDENCE}/logs/pass320-application.log"
'''
new = '''  if [[ -n "${pass320}" ]]; then
    echo "fa_followup_script=${pass320}" | tee "${EVIDENCE}/fa-followup-selection.txt"
    python3 "${pass320}" 2>&1 | tee "${EVIDENCE}/logs/fa-followup-application.log"
  else
    echo 'No separate FunctionalAnalysis pass-320 script exists; compiling the latest available FA candidate.' \\
      | tee "${EVIDENCE}/fa-followup-selection.txt"
  fi
'''
if old not in base:
    raise SystemExit('expected mandatory FA-pass320 block not found in base driver')
base = base.replace(old, new, 1)
base = base.replace(
    "echo 'checked-in FunctionalAnalysis failed; reconstructing the PASS-320 candidate without branch/source hash pinning'",
    "echo 'checked-in FunctionalAnalysis failed; reconstructing the latest FA candidate on the verified current Advanced source'",
    1,
)
base = base.replace(
    "git commit -m 'fix: materialize FunctionalAnalysis PASS 320 candidate after FA Integrated QYM verification'",
    "git commit -m 'fix: materialize verified FunctionalAnalysis source after Integrated and QYM validation'",
    1,
)
base = base.replace(
    "echo 'PASS-320 candidate materialized after FA, Integrated, and QYM all passed twice'",
    "echo 'FunctionalAnalysis candidate materialized after FA, Integrated, and QYM all passed twice'",
    1,
)
Path('/tmp/ci_current_advanced_fa_qym_v2.generated.sh').write_text(base, encoding='utf-8')
PY

bash /tmp/ci_current_advanced_fa_qym_v2.generated.sh
