#!/usr/bin/env bash
set -euo pipefail
python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa465_candidate_ci.sh');dst=Path('/tmp/fa466_candidate_ci.sh');text=src.read_text()
text=text.replace('build-logs/fa465-checked-lower','build-logs/fa466-selectedscale')
text=text.replace('scripts/fa465_prepare_checked_lower.py','scripts/fa466_prepare_selectedscale.py')
dst.write_text(text)
PY
exec bash /tmp/fa466_candidate_ci.sh
