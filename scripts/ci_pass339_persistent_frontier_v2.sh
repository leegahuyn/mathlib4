#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/ci_pass339_persistent_frontier.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source = Path('scripts/ci_pass339_persistent_frontier.sh').read_text(encoding='utf-8')
old = '''# Promote only onto the latest PR9 head, then re-run the complete two-pass chain.
git fetch origin "refs/heads/${TARGET_BRANCH}:refs/remotes/origin/${TARGET_BRANCH}"
git checkout --detach "refs/remotes/origin/${TARGET_BRANCH}"
'''
new = '''# Promote only onto the latest PR9 head, then re-run the complete two-pass chain.
# The verified sources are already copied to /tmp. Clear the successful frontier
# worktree before switching refs so local changes cannot block checkout.
git reset --hard HEAD
git clean -fd --exclude=.lake
git fetch origin "refs/heads/${TARGET_BRANCH}:refs/remotes/origin/${TARGET_BRANCH}"
git checkout --detach "refs/remotes/origin/${TARGET_BRANCH}"
'''
count = source.count(old)
print(f'promotion checkout reset: expected=1 actual={count}')
if count != 1:
    raise SystemExit(f'expected one promotion checkout block, found {count}')
source = source.replace(old, new)
out = Path('/tmp/ci_pass339_persistent_frontier_v2.generated.sh')
out.write_text(source, encoding='utf-8')
out.chmod(0o755)
PY
bash -n /tmp/ci_pass339_persistent_frontier_v2.generated.sh
exec bash /tmp/ci_pass339_persistent_frontier_v2.generated.sh
