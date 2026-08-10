#!/usr/bin/env bash
set -euo pipefail
python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa459_candidate_ci.sh')
dst=Path('/tmp/fa459_gl_candidate_ci.sh')
text=src.read_text(encoding='utf-8')
old='python3 scripts/fa459_prepare_true_first_cluster.py'
new='python3 scripts/fa459_prepare_gl_invariant.py'
if text.count(old) != 1:
    raise SystemExit(f'INFRA_FAILURE: expected one candidate preparer call, found {text.count(old)}')
dst.write_text(text.replace(old,new,1),encoding='utf-8')
PY
exec bash /tmp/fa459_gl_candidate_ci.sh
