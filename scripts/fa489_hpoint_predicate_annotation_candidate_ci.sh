#!/usr/bin/env bash
set -euo pipefail

export FA488_EVIDENCE_RUN_ID=31455142823
export FA488_EVIDENCE_JOB_ID=93667256223
export FA488_EVIDENCE_HEAD_SHA=7b41dc35cd137fe8827331e7a514b50e85546ce7
export FA488_EVIDENCE_SOURCE_SHA256=701d7a7218cb73aeded5090f813487d07f384f38a08b67a0a9518f1dd54ef89a
export FA488_FIRST_ERROR_LINE=35311
export FA488_FIRST_ERROR_COL=59
export FA488_FRONTIER_DECLARATION=selectedLogHeightEnergyDensity_continuous
export FA488_FRONTIER_INDEX=2806
export FA489_VARIANT=annotate_predicate_lambda

python3 - <<'PY'
from pathlib import Path
src=Path('scripts/fa488_hpoint_explicit_complex_candidate_ci.sh')
dst=Path('/tmp/fa489_hpoint_predicate_annotation_candidate_ci.sh')
text=src.read_text(encoding='utf-8')

def once(old,new):
    global text
    n=text.count(old)
    if n != 1: raise RuntimeError(f'expected one {old!r}, found {n}')
    text=text.replace(old,new,1)

once('build-logs/codex-fa488-hpoint-explicit-complex','build-logs/codex-fa489-hpoint-predicate-annotation')
once('scripts/fa488_prepare_hpoint_explicit_complex.py','scripts/fa489_prepare_hpoint_predicate_annotation.py')
once('/tmp/fa488_hpoint_explicit_complex_candidate_ci.sh','/tmp/fa489_inner_candidate_ci.sh')
dst.write_text(text,encoding='utf-8')
PY

exec bash /tmp/fa489_hpoint_predicate_annotation_candidate_ci.sh
