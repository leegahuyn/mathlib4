#!/usr/bin/env bash
set -euo pipefail

export FA500_EVIDENCE_RUN_ID=31470489635
export FA500_EVIDENCE_JOB_ID=93712581127
export FA500_EVIDENCE_HEAD_SHA=bbda106c0fafed1dcc64ed4dc7ce84728fac12b5
export FA500_EVIDENCE_SOURCE_SHA256=1227fa3cfc64d930aab57e883725380944444100844200161156e6bfbf60f22c
export FA500_FIRST_ERROR_LINE=35735
export FA500_FIRST_ERROR_COL=8
export FA500_FRONTIER_DECLARATION=selectedHeightGraphDensity_uniform_eventually_zero
export FA500_FRONTIER_INDEX=2825
export FA501_VARIANT=simp_only_hlevel
export FA_COMPILE_MAX_ERRORS="${FA_COMPILE_MAX_ERRORS:-1}"

python3 - <<'PY'
from pathlib import Path
src = Path('scripts/fa500_ofcomplex_source_membership_candidate_ci.sh')
dst = Path('/tmp/fa501_height_density_dependent_hlevel_candidate_ci.sh')
text = src.read_text(encoding='utf-8')
def once(old: str, new: str):
    global text
    if text.count(old) != 1:
        raise RuntimeError(f'expected one {old!r}, got {text.count(old)}')
    text = text.replace(old, new, 1)
once('build-logs/codex-fa500-ofcomplex-source-membership', 'build-logs/codex-fa501-height-density-dependent-hlevel')
once('scripts/fa500_prepare_ofcomplex_source_membership.py', 'scripts/fa501_prepare_height_density_dependent_hlevel.py')
dst.write_text(text, encoding='utf-8')
PY

exec bash /tmp/fa501_height_density_dependent_hlevel_candidate_ci.sh
