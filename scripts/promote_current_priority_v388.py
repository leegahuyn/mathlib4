from __future__ import annotations

import json
from pathlib import Path

import pass383_marker_watcher as watcher

ROOT = Path(__file__).resolve().parents[1]
BRANCH = 'fix/fa388-diverse-model-chain-20260809'
OUT = ROOT / 'build-logs' / 'PASS388_PROMOTION.json'


def main() -> int:
    verification = watcher.verify_two_rounds(ROOT)
    if not verification.get('pass'):
        result = {
            'pass': False,
            'reason': 'current PASS 388 branch failed independent two-round verification',
            'verification': verification,
        }
    else:
        result = watcher.promote(BRANCH, ROOT, verification)
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result, indent=2))
    return 0 if result.get('pass') else 2


if __name__ == '__main__':
    raise SystemExit(main())
