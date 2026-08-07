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
    "BRANCH='fix/primality-sheaf-clean-build'\n",
    "BRANCH='ci/fa319-isolated-20260807'\n",
    'isolated verification branch',
)
source = replace_once(
    source,
    "EVIDENCE='/tmp/fa318-qym-x86'\n",
    "EVIDENCE='/tmp/fa323-qym'\n",
    'pass323 evidence directory',
)
source = replace_once(
    source,
    "EXPECTED_FA_PASS318_SHA256='a61e8c20bdc28395d6b71857ec714780e36e8d98233480226e0442098ae3a438'\n",
    "EXPECTED_FA_PASS318_SHA256='a61e8c20bdc28395d6b71857ec714780e36e8d98233480226e0442098ae3a438'\n"
    "EXPECTED_FA_PASS319_SHA256='171588d37133a6494727645474dadad3f80828bdcf8a1ce5b8fd72b77d4d3c0a'\n"
    "EXPECTED_FA_PASS320_SHA256='48fe6bd80915c155b6a38266c7a30f3818ad4b335fb9b77cc07175c8cad1dcd9'\n"
    "EXPECTED_FA_PASS321_SHA256='d184ee500fb6d514db79e50d4ed581cba0123660e0f8288d6f479e6f1c63d51f'\n"
    "EXPECTED_FA_PASS322_SHA256='5f7052b75353817e55e4fab35cc5f6578a9449737476a3dd05621999eaa67eed'\n",
    'pass323 predecessor hashes',
)
source = replace_once(
    source,
    '''if [[ "${fa_blob}" = "${EXPECTED_FA_BASELINE_BLOB}" ]]; then
  source_state='baseline'
elif [[ "${fa_sha}" = "${EXPECTED_FA_PASS318_SHA256}" ]]; then
  source_state='materialized'
else
  echo "unexpected FA source blob=${fa_blob} sha256=${fa_sha}" >&2
  exit 1
fi
''',
    '''if [[ "${fa_blob}" = "${EXPECTED_FA_BASELINE_BLOB}" ]]; then
  source_state='baseline'
else
  # A non-baseline source is never repaired in this run.  It must pass the
  # trust audit and two direct compiles exactly as checked in.
  source_state='materialized'
fi
''',
    'direct-source materialized selection',
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
  python3 scripts/apply_three_hundred_twentieth_pass_functional_analysis_repairs.py \\
    2>&1 | tee "${EVIDENCE}/logs/pass320-application.log"
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${EXPECTED_FA_PASS320_SHA256}"
  python3 scripts/apply_three_hundred_twenty_first_pass_functional_analysis_repairs.py \\
    2>&1 | tee "${EVIDENCE}/logs/pass321-application.log"
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${EXPECTED_FA_PASS321_SHA256}"
  python3 scripts/apply_three_hundred_twenty_second_pass_functional_analysis_repairs.py \\
    2>&1 | tee "${EVIDENCE}/logs/pass322-application.log"
  test "$(sha256sum "${FA}" | awk '{print $1}')" = "${EXPECTED_FA_PASS322_SHA256}"
  python3 scripts/apply_three_hundred_twenty_third_pass_functional_analysis_repairs.py \\
    2>&1 | tee "${EVIDENCE}/logs/pass323-application.log"
  pass323_sha="$(sha256sum "${FA}" | awk '{print $1}')"
  test "${pass323_sha}" != "${EXPECTED_FA_PASS322_SHA256}"
  echo "pass323_sha256=${pass323_sha}" | tee "${EVIDENCE}/pass323-sha256.txt"
fi
cp "${FA}" "${EVIDENCE}/source/Mock2_FunctionalAnalysis.pass323.lean"
''',
    'pass323 application and evidence source',
)
source = replace_once(
    source,
    "  git commit -m 'fix: materialize Mock2 FunctionalAnalysis pass 318 source'\n",
    "  git commit -m 'fix: materialize Mock2 FunctionalAnalysis pass 323 source'\n",
    'pass323 materialization commit',
)
Path('/tmp/ci_fa323_qym.generated.sh').write_text(source, encoding='utf-8')
PY

bash /tmp/ci_fa323_qym.generated.sh
