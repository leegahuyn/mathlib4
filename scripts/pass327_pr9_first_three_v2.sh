#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/pass327_pr9_first_three.sh'
test -f "${BASE}"

python3 - <<'PY'
from pathlib import Path

path = Path('scripts/pass327_pr9_first_three.sh')
source = path.read_text(encoding='utf-8')
old = '''  git fetch --depth=1 origin "${ADVANCED_BASELINE_COMMIT}"
  git fetch --depth=1 origin "${FA_BASELINE_COMMIT}"
'''
new = '''  # Fetch both historical baselines in one transaction. Two consecutive
  # shallow fetches can race while rewriting .git/shallow on hosted runners.
  git -c fetch.writeCommitGraph=false fetch \\
    --no-tags --no-recurse-submodules origin \\
    "${ADVANCED_BASELINE_COMMIT}" "${FA_BASELINE_COMMIT}"
'''
count = source.count(old)
print(f'PASS327 baseline fetch replacement: expected=1 actual={count}')
if count != 1:
    raise SystemExit(f'expected one sequential shallow-fetch block, found {count}')
source = source.replace(old, new)
out = Path('/tmp/pass327_pr9_first_three_v2.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY

bash -n /tmp/pass327_pr9_first_three_v2.generated.sh
exec bash /tmp/pass327_pr9_first_three_v2.generated.sh
