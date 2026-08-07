#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/ci_fa318_qym.sh'
EXPECTED_BASE_BLOB='76828a0431ca5240bf9eee2bca43b02548f64980'
test "$(git hash-object "${BASE}")" = "${EXPECTED_BASE_BLOB}"

python3 - <<'PY'
from pathlib import Path

source = Path('scripts/ci_fa318_qym.sh').read_text(encoding='utf-8')


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    print(f'{label}: expected=1 actual={count}')
    if count != 1:
        raise RuntimeError(f'{label}: expected one occurrence, found {count}')
    return text.replace(old, new)

source = replace_once(
    source,
    "EVIDENCE='/tmp/fa318-qym-x86'\n",
    "EVIDENCE='/tmp/fa319-qym-x86'\n",
    'pass319 evidence directory',
)
source = replace_once(
    source,
    "EXPECTED_FA_PASS318_SHA256='a61e8c20bdc28395d6b71857ec714780e36e8d98233480226e0442098ae3a438'\n",
    "EXPECTED_FA_PASS318_SHA256='a61e8c20bdc28395d6b71857ec714780e36e8d98233480226e0442098ae3a438'\n"
    "EXPECTED_FA_PASS319_SHA256='171588d37133a6494727645474dadad3f80828bdcf8a1ce5b8fd72b77d4d3c0a'\n",
    'pass319 expected source hash',
)
source = replace_once(
    source,
    '''elif [[ "${fa_sha}" = "${EXPECTED_FA_PASS318_SHA256}" ]]; then
  source_state='materialized'
''',
    '''elif [[ "${fa_sha}" = "${EXPECTED_FA_PASS319_SHA256}" ]]; then
  source_state='materialized'
''',
    'pass319 materialized source selection',
)
source = replace_once(
    source,
    '''  python3 scripts/apply_three_hundred_eighteenth_pass_functional_analysis_repairs.py \\
    2>&1 | tee "${EVIDENCE}/logs/pass318-application.log"
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${EXPECTED_FA_PASS318_SHA256}"
fi
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis.pass318.lean"
''',
    '''  python3 scripts/apply_three_hundred_eighteenth_pass_functional_analysis_repairs.py \\
    2>&1 | tee "${EVIDENCE}/logs/pass318-application.log"
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${EXPECTED_FA_PASS318_SHA256}"
  python3 scripts/apply_three_hundred_nineteenth_pass_functional_analysis_repairs.py \\
    2>&1 | tee "${EVIDENCE}/logs/pass319-application.log"
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${EXPECTED_FA_PASS319_SHA256}"
fi
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis.pass319.lean"
''',
    'pass319 application and evidence source',
)
source = replace_once(
    source,
    "  git commit -m 'fix: materialize Mock2 FunctionalAnalysis pass 318 source'\n",
    "  git commit -m 'fix: materialize Mock2 FunctionalAnalysis pass 319 source'\n",
    'pass319 materialization commit',
)
Path('/tmp/ci_fa319_qym.generated.sh').write_text(source, encoding='utf-8')
PY

bash /tmp/ci_fa319_qym.generated.sh
