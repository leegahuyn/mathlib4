#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/ci_pass327_full_order_v3.sh'
GENERATED='/tmp/ci_pass327_full_order_v4.generated.sh'
test -s "${BASE}"

python3 - "${BASE}" "${GENERATED}" <<'PY'
from pathlib import Path
import sys
source=Path(sys.argv[1]).read_text(encoding='utf-8')
start=source.index('for path in \\\n  PrimalitySheafVerification/Mock2_Advanced.lean')
end=source.index('while IFS= read -r path; do copy_to_pr7',start)
replacement='''for path in \\
  PrimalitySheafVerification/Spt1.lean \\
  PrimalitySheafVerification/Spt2.lean \\
  PrimalitySheafVerification/Spt3.lean \\
  PrimalitySheafVerification/Spt4.lean \\
  PrimalitySheafVerification/Spt5.lean \\
  PrimalitySheafVerification/Spt6.lean \\
  PrimalitySheafVerification/Spt7.lean \\
  PrimalitySheafVerification/Mock1.lean \\
  PrimalitySheafVerification/Mock1_Advanced.lean \\
  PrimalitySheafVerification/Mock2.lean \\
  PrimalitySheafVerification/Mock2_Advanced.lean \\
  PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean \\
  PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean \\
  PrimalitySheafVerification/QYM.lean \\
  PrimalitySheafVerification/BuildAll.lean \\
  scripts/primality_final_local_gate.sh \\
  scripts/primality_final_local_gate_v2.sh \\
  scripts/generate_spt5_whole_file_audit.py \\
  scripts/install_primality_official_ci.py \\
  "${PRIORITY}" "${MOCK1}" "${FINAL_LOCAL}"; do
  copy_to_pr7 "${path}"
done
'''
source=source[:start]+replacement+source[end:]
Path(sys.argv[2]).write_text(source,encoding='utf-8')
PY

bash -n "${GENERATED}"
bash "${GENERATED}"
