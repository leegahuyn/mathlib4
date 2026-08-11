#!/usr/bin/env bash
set -euo pipefail

export FA504_EVIDENCE_RUN_ID=31476200843
export FA504_EVIDENCE_JOB_ID=93730366964
export FA504_EVIDENCE_HEAD_SHA=abb10a69c70e9077f17ca7aa9f27f3ca63f31070
export FA504_EVIDENCE_SOURCE_SHA256=57d05b04902887e305dcc34c4193a72747540292ee690a087ee958d771203c18
export FA504_FIRST_ERROR_LINE=36042
export FA504_FIRST_ERROR_COL=2
export FA504_FRONTIER_DECLARATION=integral_selectedHeightGraphDensity_stripTail_eq_iterated
export FA504_FRONTIER_INDEX=2835
export FA505_VARIANT=reuse_verified_prod_restrict_rewrite
export FA_COMPILE_MAX_ERRORS="${FA_COMPILE_MAX_ERRORS:-32}"

python3 - <<'PY'
from pathlib import Path

src = Path('scripts/fa504_joint_basepoint_source_membership_candidate_ci.sh')
dst = Path('/tmp/fa505_height_graph_strip_fubini_candidate_ci.sh')
text = src.read_text(encoding='utf-8')


def once(old: str, new: str) -> None:
    global text
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'expected one {old!r}, got {count}')
    text = text.replace(old, new, 1)


once(
    'build-logs/codex-fa504-joint-basepoint-source-membership',
    'build-logs/codex-fa505-height-graph-strip-fubini',
)
once(
    'scripts/fa504_prepare_joint_basepoint_source_membership.py',
    'scripts/fa505_prepare_height_graph_strip_fubini.py',
)
dst.write_text(text, encoding='utf-8')
PY

exec bash /tmp/fa505_height_graph_strip_fubini_candidate_ci.sh
