#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path
p=Path('scripts/fa453_selector_ci.sh')
s=p.read_text(encoding='utf-8')
old='python3 scripts/fa442_record_direct_metric.py'
new='python3 scripts/fa458_record_direct_metric_strict.py'
if s.count(old) != 1:
    raise SystemExit(f'INFRA_FAILURE: expected one selector metric recorder call, found {s.count(old)}')
p.write_text(s.replace(old,new),encoding='utf-8')
PY

exec bash scripts/fa453_selector_ci.sh
