#!/usr/bin/env bash
set -euo pipefail
BASE='scripts/diagnose_pass362_fa.sh'
test -f "${BASE}"
python3 - <<'PY'
from pathlib import Path
source=Path('scripts/diagnose_pass362_fa.sh').read_text(encoding='utf-8')
def repl(old,new,label,expected=1):
    global source
    count=source.count(old); print(f'{label}: expected={expected} actual={count}')
    if count!=expected: raise SystemExit(f'{label}: expected {expected}, found {count}')
    source=source.replace(old,new)
repl("EVIDENCE='/tmp/diagnose-pass362-fa'","EVIDENCE='/tmp/diagnose-pass363-fa'",'evidence dir')
repl('  apply_three_hundred_sixty_second_pass_functional_analysis_repairs.py; do','  apply_three_hundred_sixty_second_pass_functional_analysis_repairs.py \\\n  apply_three_hundred_sixty_third_pass_functional_analysis_repairs.py; do','pass363 chain')
repl('Mock2_FunctionalAnalysis-pass362.lean','Mock2_FunctionalAnalysis-pass363.lean','source name')
repl('Mock2_FunctionalAnalysis-pass362.log','Mock2_FunctionalAnalysis-pass363.log','log name')
Path('/tmp/diagnose_pass363_fa.generated.sh').write_text(source,encoding='utf-8')
PY
bash -n /tmp/diagnose_pass363_fa.generated.sh
exec bash /tmp/diagnose_pass363_fa.generated.sh
