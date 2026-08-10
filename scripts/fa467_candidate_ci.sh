#!/usr/bin/env bash
set -euo pipefail
: "${HORIZONTAL_STYLE:?HORIZONTAL_STYLE required}"
python3 - <<'PY'
from pathlib import Path
src = Path("scripts/fa465_candidate_ci.sh")
dst = Path("/tmp/fa467_candidate_ci.sh")
text = src.read_text(encoding="utf-8")
text = text.replace(
    "build-logs/fa465-checked-lower",
    "build-logs/codex-fa467-horizontal",
)
text = text.replace(
    "scripts/fa465_prepare_checked_lower.py",
    "scripts/fa467_prepare_horizontal_close.py",
)
dst.write_text(text, encoding="utf-8")
PY
exec bash /tmp/fa467_candidate_ci.sh
