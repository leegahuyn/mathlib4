#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import tempfile
from pathlib import Path


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--baseline', required=True)
    ap.add_argument('--output', required=True)
    ap.add_argument('--refs', required=False, default='')
    ap.add_argument('--limit', type=int, default=14)
    args = ap.parse_args()

    with tempfile.TemporaryDirectory(prefix='fa425i-') as tmp:
        tmp_dir = Path(tmp)
        cmd = [
            'python3', 'scripts/fa425g_instance_sandwich_candidates.py',
            '--baseline', args.baseline,
            '--output', str(tmp_dir),
            '--limit', '100',
        ]
        if args.refs:
            cmd += ['--refs', args.refs]
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False)
        if proc.returncode != 0:
            raise SystemExit(proc.stdout)
        manifest = json.loads((tmp_dir / 'MANIFEST.json').read_text(encoding='utf-8'))
        candidates = manifest.get('candidates', [])
        preferred = [c for c in candidates if c.get('name', '').startswith('disable-reenable-custom-')]
        secondary = [c for c in candidates if c not in preferred]
        selected = (preferred + secondary)[:args.limit]

        out = Path(args.output)
        out.mkdir(parents=True, exist_ok=True)
        rewritten = []
        for idx, item in enumerate(selected):
            old = tmp_dir / item['file']
            new_name = f"{idx:02d}-{item['name']}.lean"
            shutil.copy2(old, out / new_name)
            rewritten.append({**item, 'file': new_name})

        focused = {
            **{k: v for k, v in manifest.items() if k not in {'candidates', 'candidate_count'}},
            'strategy': 'disable custom Complex.addCommGroup before theorem and re-enable after theorem',
            'candidate_count': len(rewritten),
            'candidates': rewritten,
        }
        (out / 'MANIFEST.json').write_text(json.dumps(focused, indent=2) + '\n', encoding='utf-8')
        print(json.dumps(focused, indent=2))


if __name__ == '__main__':
    main()
