#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/primality_final_local_gate.sh'
GENERATED='/tmp/primality_final_local_gate_v2.generated.sh'
test -s "${BASE}"
test -s scripts/generate_spt5_whole_file_audit.py

python3 - "${BASE}" "${GENERATED}" <<'PY'
from pathlib import Path
import sys
source=Path(sys.argv[1]).read_text(encoding='utf-8')
start=source.index('# Generate a whole-file public declaration audit for Spt5.')
command_start=source.index("python3 - <<'PY'",start)
end_marker='\nset +e\nlake env lean .lake/Spt5WholeFileAudit.lean'
command_end=source.index(end_marker,command_start)
replacement=(
    "python3 scripts/generate_spt5_whole_file_audit.py\n"
)
source=source[:command_start]+replacement+source[command_end:]
Path(sys.argv[2]).write_text(source,encoding='utf-8')
PY

bash -n "${GENERATED}"
bash "${GENERATED}"
