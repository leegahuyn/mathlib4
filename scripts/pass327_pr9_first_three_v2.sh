#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/pass327_pr9_first_three.sh'
EXPECTED_BASE_BLOB='107f0fe240beb4da684d277046f662b6f87f0bfb'
test "$(git hash-object "${BASE}")" = "${EXPECTED_BASE_BLOB}"

python3 - <<'PY'
from pathlib import Path

path = Path('scripts/pass327_pr9_first_three.sh')
source = path.read_text(encoding='utf-8')


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    print(f'{label}: expected=1 actual={count}')
    if count != 1:
        raise RuntimeError(f'{label}: expected one occurrence, found {count}')
    return text.replace(old, new)

source = replace_once(
    source,
    '''  git fetch --depth=1 origin "${ADVANCED_BASELINE_COMMIT}"
  git fetch --depth=1 origin "${FA_BASELINE_COMMIT}"
''',
    '''  # Fetch both historical baselines in one transaction. Two consecutive
  # shallow fetches can race while rewriting .git/shallow on hosted runners.
  git -c fetch.writeCommitGraph=false fetch \\
    --no-tags --no-recurse-submodules origin \\
    "${ADVANCED_BASELINE_COMMIT}" "${FA_BASELINE_COMMIT}"
''',
    'PASS 327 baseline fetch transaction',
)
source = replace_once(
    source,
    'scripts, then apply every available FA pass through PASS324. PASS327 is the',
    'scripts, then apply every available FA pass through PASS330. PASS327 is the',
    'PASS 330 driver repair-chain comment',
)
source = replace_once(
    source,
    '''    apply_three_hundred_twenty_third_pass_functional_analysis_repairs.py \\
    apply_three_hundred_twenty_fourth_pass_functional_analysis_repairs.py; do
''',
    '''    apply_three_hundred_twenty_third_pass_functional_analysis_repairs.py \\
    apply_three_hundred_twenty_fourth_pass_functional_analysis_repairs.py \\
    apply_three_hundred_twenty_fifth_pass_functional_analysis_repairs.py \\
    apply_three_hundred_twenty_sixth_pass_functional_analysis_repairs.py \\
    apply_three_hundred_twenty_seventh_pass_functional_analysis_repairs.py \\
    apply_three_hundred_twenty_eighth_pass_functional_analysis_repairs.py \\
    apply_three_hundred_twenty_ninth_pass_functional_analysis_repairs.py \\
    apply_three_hundred_thirtieth_pass_functional_analysis_repairs.py; do
''',
    'PASS 325-330 repair-chain insertion',
)
source = replace_once(
    source,
    "  fa_mode='pass324-repaired-and-split'\n",
    "  fa_mode='pass330-repaired-and-split'\n",
    'PASS 330 verified-mode label',
)

out = Path('/tmp/pass327_pr9_first_three_v2.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY

bash -n /tmp/pass327_pr9_first_three_v2.generated.sh
exec bash /tmp/pass327_pr9_first_three_v2.generated.sh
