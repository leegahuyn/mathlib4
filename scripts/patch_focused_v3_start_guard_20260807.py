#!/usr/bin/env python3
from pathlib import Path

files = [
    Path('.github/workflows/focused-candidate-pipeline-v3-20260807.yml'),
    Path('.github/workflows/focused-direct-source-v3-20260807.yml'),
]
needle = '          test "$(git ls-remote origin "refs/heads/${BRANCH}" | awk \'{print $1}\')" = "${GITHUB_SHA}"\n'
for path in files:
    text = path.read_text(encoding='utf-8')
    if needle in text:
        text = text.replace(needle, '')
    path.write_text(text, encoding='utf-8')

for path in files:
    text = path.read_text(encoding='utf-8')
    if 'test "$(git ls-remote origin "refs/heads/${BRANCH}"' in text:
        raise SystemExit(f'stale start-head guard remains in {path}')
