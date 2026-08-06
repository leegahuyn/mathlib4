#!/usr/bin/env python3
from pathlib import Path

path=Path('.github/workflows/focused-candidate-v4-20260807.yml')
text=path.read_text(encoding='utf-8')
anchor='''      - name: Upload candidate proof artifact
        if: always()
        uses: actions/upload-artifact@v4
'''
replacement='''      - name: Upload candidate proof artifact
        if: always()
        continue-on-error: true
        uses: actions/upload-artifact@v4
'''
if anchor in text:
    text=text.replace(anchor,replacement)
path.write_text(text,encoding='utf-8')
if 'continue-on-error: true\n        uses: actions/upload-artifact@v4' not in path.read_text(encoding='utf-8'):
    raise SystemExit('candidate artifact resilience patch missing')
