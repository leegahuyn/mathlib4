#!/usr/bin/env python3
from pathlib import Path

patches = {
    Path('.github/workflows/focused-candidate-pipeline-v3-20260807.yml'): (
        '          bash scripts/focused_materialize_pipeline_20260807.sh\n',
        '          bash scripts/run_focused_candidate_v3_20260807.sh\n',
    ),
    Path('.github/workflows/focused-direct-source-v3-20260807.yml'): (
        '          bash scripts/focused_direct_verify_20260807.sh\n',
        '          bash scripts/run_focused_direct_v3_20260807.sh\n',
    ),
}

for path, (old, new) in patches.items():
    text = path.read_text(encoding='utf-8')
    if old in text:
        text = text.replace(old, new)
    marker = '      - name: Upload '
    index = text.find(marker)
    if index < 0:
        raise SystemExit(f'upload step not found in {path}')
    with_if = marker + ('candidate proof artifact before source materialization\n'
                        if 'candidate-pipeline' in path.name
                        else 'direct-source proof artifact\n') + '        if: always()\n'
    original = marker + ('candidate proof artifact before source materialization\n'
                          if 'candidate-pipeline' in path.name
                          else 'direct-source proof artifact\n')
    if original in text and with_if not in text:
        text = text.replace(original, with_if)
    path.write_text(text, encoding='utf-8')

for path, (_, wrapper) in patches.items():
    text = path.read_text(encoding='utf-8')
    if wrapper.strip() not in text:
        raise SystemExit(f'wrapper handoff missing in {path}')
    if 'if: always()' not in text:
        raise SystemExit(f'always-upload guard missing in {path}')
