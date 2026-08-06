#!/usr/bin/env python3
from pathlib import Path

FILES = [
    Path('.github/workflows/focused-m2a-v68-materialize-20260807.yml'),
    Path('.github/workflows/focused-m2a-direct-source-20260807.yml'),
    Path('.github/workflows/focused-functional-analysis-materialize-20260807.yml'),
    Path('.github/workflows/focused-functional-analysis-direct-20260807.yml'),
    Path('.github/workflows/focused-qym-direct-20260807.yml'),
]

for path in FILES:
    if not path.is_file():
        raise SystemExit(f'missing focused workflow: {path}')
    text = path.read_text(encoding='utf-8')
    text = text.replace('LOGDIR: focused-proof/', 'LOGDIR: /tmp/focused-proof/')
    text = text.replace(
        "Path('focused-proof/Mock2_Advanced-direct/direct-pass.json')",
        "Path('/tmp/focused-proof/Mock2_Advanced-direct/direct-pass.json')",
    )
    text = text.replace(
        "Path('focused-proof/FunctionalAnalysis-direct/direct-pass.json')",
        "Path('/tmp/focused-proof/FunctionalAnalysis-direct/direct-pass.json')",
    )
    text = text.replace(
        "Path('focused-proof/QYM-direct/direct-pass.json')",
        "Path('/tmp/focused-proof/QYM-direct/direct-pass.json')",
    )
    text = text.replace(
        'git clone --no-hardlinks . "$dir" >/dev/null',
        'git clone --no-hardlinks "${GITHUB_WORKSPACE}" "$dir" >/dev/null',
    )
    if path.name == 'focused-m2a-v68-materialize-20260807.yml':
        old = (
            'cmp -s /tmp/m2a-repro-a/"${TARGET}" /tmp/m2a-repro-b/"${TARGET}"\n'
            '          cp /tmp/m2a-repro-a/"${TARGET}" "${TARGET}"'
        )
        new = (
            'cmp -s /tmp/m2a-repro-a/"${TARGET}" /tmp/m2a-repro-b/"${TARGET}"\n'
            '          cd "${GITHUB_WORKSPACE}"\n'
            '          cp /tmp/m2a-repro-a/"${TARGET}" "${TARGET}"'
        )
        if old in text:
            text = text.replace(old, new)
    if path.name == 'focused-functional-analysis-materialize-20260807.yml':
        old = (
            'cmp -s /tmp/fa-repro-a/"${FA}" /tmp/fa-repro-b/"${FA}"\n'
            '          cp /tmp/fa-repro-a/"${FA}" "${FA}"'
        )
        new = (
            'cmp -s /tmp/fa-repro-a/"${FA}" /tmp/fa-repro-b/"${FA}"\n'
            '          cd "${GITHUB_WORKSPACE}"\n'
            '          cp /tmp/fa-repro-a/"${FA}" "${FA}"'
        )
        if old in text:
            text = text.replace(old, new)
    path.write_text(text, encoding='utf-8')

for path in FILES:
    text = path.read_text(encoding='utf-8')
    if 'LOGDIR: focused-proof/' in text:
        raise SystemExit(f'worktree-local proof path remains in {path}')

for name in [
    'focused-m2a-v68-materialize-20260807.yml',
    'focused-functional-analysis-materialize-20260807.yml',
]:
    text = Path('.github/workflows', name).read_text(encoding='utf-8')
    if 'git clone --no-hardlinks "${GITHUB_WORKSPACE}" "$dir"' not in text:
        raise SystemExit(f'workspace clone fix missing in {name}')
    if 'cd "${GITHUB_WORKSPACE}"' not in text:
        raise SystemExit(f'candidate copy-back fix missing in {name}')
