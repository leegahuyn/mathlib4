#!/usr/bin/env bash
set -euo pipefail

BASE='scripts/ci_pass327_full_order_v3.sh'
GENERATED='/tmp/ci_pass327_full_order_v7.generated.sh'
test -s "${BASE}"
for required in \
  scripts/ci_pass327_fa_qym_recovery_v2.sh \
  scripts/pass327_lean_repair_agent_v2.py \
  scripts/post_priority_lean_repair_agent_v2.py \
  scripts/final_dependency_repair_agent_v2.py; do
  test -s "${required}"
done

python3 - "${BASE}" "${GENERATED}" <<'PY'
from pathlib import Path
import sys
source=Path(sys.argv[1]).read_text(encoding='utf-8')
replacements={
 'bash scripts/ci_pass327_fa_qym_recovery.sh':'bash scripts/ci_pass327_fa_qym_recovery_v2.sh',
 'python3 scripts/pass327_lean_repair_agent.py':'python3 scripts/pass327_lean_repair_agent_v2.py',
 'python3 scripts/post_priority_lean_repair_agent.py':'python3 scripts/post_priority_lean_repair_agent_v2.py',
 'python3 scripts/final_dependency_repair_agent.py':'python3 scripts/final_dependency_repair_agent_v2.py',
}
for old,new in replacements.items():
    count=source.count(old)
    if count!=1: raise RuntimeError(f'expected one {old!r}, found {count}')
    source=source.replace(old,new)

old_case='''      0)
        ;;
      20)
        stage_and_commit \\
          'wip: preserve recovered PASS 327 Advanced and FA candidates' \\
          "${priority_paths[@]}"
        ;;
'''
new_case='''      0)
        stage_and_commit \\
          'fix: preserve directly verified PASS 327 priority sources' \\
          "${priority_paths[@]}" "${PRIORITY}"
        ;;
      20)
        stage_and_commit \\
          'wip: preserve recovered PASS 327 Advanced and FA candidates' \\
          "${priority_paths[@]}"
        ;;
'''
if source.count(old_case)!=1:
    raise RuntimeError(f'PASS recovery case block count={source.count(old_case)}')
source=source.replace(old_case,new_case)

copy_function=source.index('copy_to_pr7() {')
start=source.index('for path in ',copy_function)
end=source.index('while IFS= read -r path; do copy_to_pr7',start)
paths=[
 'PrimalitySheafVerification/Spt1.lean','PrimalitySheafVerification/Spt2.lean',
 'PrimalitySheafVerification/Spt3.lean','PrimalitySheafVerification/Spt4.lean',
 'PrimalitySheafVerification/Spt5.lean','PrimalitySheafVerification/Spt6.lean',
 'PrimalitySheafVerification/Spt7.lean','PrimalitySheafVerification/Mock1.lean',
 'PrimalitySheafVerification/Mock1_Advanced.lean','PrimalitySheafVerification/Mock2.lean',
 'PrimalitySheafVerification/Mock2_Advanced.lean',
 'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean',
 'PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean',
 'PrimalitySheafVerification/QYM.lean','PrimalitySheafVerification/BuildAll.lean',
 'scripts/primality_final_local_gate.sh','scripts/primality_final_local_gate_v2.sh',
 'scripts/generate_spt5_whole_file_audit.py','scripts/install_primality_official_ci.py',
]
array='transfer_paths=(\n'+''.join(f'  {path}\n' for path in paths)+')\n'
loop=(
    array
    +'for path in "${transfer_paths[@]}" "${PRIORITY}" "${MOCK1}" "${FINAL_LOCAL}"; do\n'
    +'  copy_to_pr7 "${path}"\n'
    +'done\n'
)
source=source[:start]+loop+source[end:]
Path(sys.argv[2]).write_text(source,encoding='utf-8')
PY

bash -n "${GENERATED}"
bash "${GENERATED}"
