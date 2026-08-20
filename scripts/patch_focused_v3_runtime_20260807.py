#!/usr/bin/env python3
from pathlib import Path

candidate = Path('scripts/focused_materialize_pipeline_20260807.sh')
text = candidate.read_text(encoding='utf-8')

text = text.replace(
    "compile_or_fail Mock2 'phase-b-Mock2-prerequisite'\n"
    "compile_or_fail Mock2_Advanced 'phase-b-M2A-prerequisite'\n\n",
    "# Phase A leaves verified Mock2 and Mock2_Advanced objects in place.\n\n",
)

old_unsplit = """  python3 \"${AUDITOR}\" audit \"${FA}\" > \"${LOGDIR}/phase-b-FA-unsplit-static-trust.json\"
  for pass in 1 2; do
    compile_or_fail Mock2 \"phase-b-unsplit-Mock2-pass${pass}\"
    compile_or_fail Mock2_Advanced \"phase-b-unsplit-M2A-pass${pass}\"
    compile_or_fail Mock2_FunctionalAnalysis \"phase-b-FA-unsplit-candidate-pass${pass}\"
  done
  cp \"${FA}\" \"${INTEGRATED}\"
"""
new_unsplit = """  python3 \"${AUDITOR}\" audit \"${FA}\" > \"${LOGDIR}/phase-b-FA-unsplit-static-trust.json\"
  # The final candidate module is the substantive Integrated source.  It is
  # compiled twice below after materialization; compiling the temporary
  # historical path twice here would duplicate the same 60k-line proof body.
  cp \"${FA}\" \"${INTEGRATED}\"
"""
if old_unsplit not in text:
    raise SystemExit('unsplit duplicate-compile block not found')
text = text.replace(old_unsplit, new_unsplit)

old_integrated = """for pass in 1 2; do
  compile_or_fail Mock2 \"phase-c-Mock2-regression-pass${pass}\"
  compile_or_fail Mock2_Advanced \"phase-c-M2A-regression-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis_Integrated \"phase-c-Integrated-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis \"phase-c-FA-wrapper-pass${pass}\"
done
"""
new_integrated = """for pass in 1 2; do
  compile_or_fail Mock2_FunctionalAnalysis_Integrated \"phase-c-Integrated-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis \"phase-c-FA-wrapper-pass${pass}\"
done
"""
if old_integrated not in text:
    raise SystemExit('Integrated duplicate dependency block not found')
text = text.replace(old_integrated, new_integrated)

old_qym = """for pass in 1 2; do
  compile_or_fail Mock2 \"phase-d-Mock2-regression-pass${pass}\"
  compile_or_fail Mock2_Advanced \"phase-d-M2A-regression-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis_Integrated \"phase-d-Integrated-regression-pass${pass}\"
  compile_or_fail Mock2_FunctionalAnalysis \"phase-d-FA-regression-pass${pass}\"
  compile_or_fail QYM \"phase-d-QYM-pass${pass}\"
done
"""
new_qym = """for pass in 1 2; do
  compile_or_fail QYM \"phase-d-QYM-pass${pass}\"
done
"""
if old_qym not in text:
    raise SystemExit('QYM duplicate dependency block not found')
text = text.replace(old_qym, new_qym)
candidate.write_text(text, encoding='utf-8')

for workflow_name in [
    '.github/workflows/focused-candidate-pipeline-v3-20260807.yml',
    '.github/workflows/focused-direct-source-v3-20260807.yml',
]:
    path = Path(workflow_name)
    workflow = path.read_text(encoding='utf-8').replace('timeout-minutes: 480', 'timeout-minutes: 360')
    path.write_text(workflow, encoding='utf-8')

if 'phase-b-unsplit-Mock2-pass' in candidate.read_text(encoding='utf-8'):
    raise SystemExit('duplicate unsplit dependency compile remains')
if 'phase-d-M2A-regression-pass' in candidate.read_text(encoding='utf-8'):
    raise SystemExit('duplicate QYM dependency compile remains')
