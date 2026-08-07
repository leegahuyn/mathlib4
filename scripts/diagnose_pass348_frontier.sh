#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path
path = Path('scripts/diagnose_pass341_fa.sh')
text = path.read_text(encoding='utf-8')
old = '-DmaxErrors=2000'
new = '-DmaxErrors=50'
count = text.count(old)
print(f'frontier maxErrors rewrite: expected=1 actual={count}')
if count != 1:
    raise SystemExit(f'expected one maxErrors setting, found {count}')
path.write_text(text.replace(old, new), encoding='utf-8')
PY

exec bash scripts/diagnose_pass348_fa.sh
