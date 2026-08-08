from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
OUT = Path('/tmp/pass378')
OUT.mkdir(parents=True, exist_ok=True)


def targets() -> list[Path]:
    base = ROOT / 'PrimalitySheafVerification'
    result = [
        base / 'Mock2_FunctionalAnalysis.lean',
        base / 'Mock2_FunctionalAnalysis_Integrated.lean',
    ]
    bridges = sorted(
        p for p in base.glob('Mock3*.lean')
        if not any(token in p.name.lower() for token in ('backup', 'candidate', 'probe', 'tmp'))
    )
    result.extend(bridges)
    result.append(base / 'QYM.lean')
    return result


def module_name(path: Path) -> str:
    return str(path.relative_to(ROOT).with_suffix('')).replace('/', '.')


def artifact_paths(path: Path) -> list[Path]:
    rel = path.relative_to(ROOT).with_suffix('')
    base = ROOT / '.lake' / 'build' / 'lib' / 'lean' / rel
    return [base.with_suffix('.olean'), base.with_suffix('.ilean')]


def source_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compile_one(path: Path, label: str, max_errors: int = 120) -> dict[str, Any]:
    for artifact in artifact_paths(path):
        artifact.unlink(missing_ok=True)
    log = OUT / f'{path.stem}-{label}.log'
    env = os.environ.copy()
    env['PATH'] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    start = time.monotonic()
    try:
        proc = subprocess.run(
            ['lake', 'env', 'lean', f'-DmaxErrors={max_errors}', str(path.relative_to(ROOT))],
            cwd=ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=1800,
            check=False,
        )
        output = proc.stdout
        rc = proc.returncode
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or '') + '\n[priority-chain] timeout\n'
        rc = 124
    log.write_text(output, encoding='utf-8')
    matches = list(re.finditer(r'^.*?\.lean:(\d+):(\d+): error:\s*(.*)$', output, re.M))
    artifacts_ok = all(p.is_file() and p.stat().st_size > 0 for p in artifact_paths(path)) if rc == 0 else False
    return {
        'path': str(path.relative_to(ROOT)),
        'module': module_name(path),
        'label': label,
        'exit_code': rc,
        'error_headers': len(matches),
        'first_error_line': int(matches[0].group(1)) if matches else None,
        'first_error_col': int(matches[0].group(2)) if matches else None,
        'first_error_message': matches[0].group(3).strip() if matches else '',
        'artifacts_ok': artifacts_ok,
        'source_sha256': source_sha(path),
        'elapsed_seconds': round(time.monotonic() - start, 2),
        'log': str(log),
    }


def verify_target(path: Path, runs: int) -> dict[str, Any]:
    records = []
    for run in range(1, runs + 1):
        record = compile_one(path, f'run{run}')
        records.append(record)
        if record['exit_code'] != 0 or not record['artifacts_ok']:
            break
    return {
        'path': str(path.relative_to(ROOT)),
        'pass': len(records) == runs and all(r['exit_code'] == 0 and r['artifacts_ok'] for r in records),
        'runs': records,
    }


def prepare_prerequisites(target: Path) -> list[dict[str, Any]]:
    chain = targets()
    if target not in chain:
        raise SystemExit(f'target is outside the priority chain: {target}')
    records = []
    for path in chain[:chain.index(target)]:
        if not path.exists():
            raise SystemExit(f'missing prerequisite: {path}')
        record = compile_one(path, 'prerequisite', max_errors=200)
        records.append(record)
        if record['exit_code'] != 0 or not record['artifacts_ok']:
            raise SystemExit(f'prerequisite failed: {path}: {record}')
    return records


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--mode', choices=('select', 'prepare', 'verify'), required=True)
    parser.add_argument('--target')
    parser.add_argument('--runs', type=int, default=2)
    args = parser.parse_args()

    chain = targets()
    if args.mode == 'select':
        missing = [str(p.relative_to(ROOT)) for p in chain if not p.exists()]
        if missing:
            payload = {'all_pass': False, 'missing': missing, 'selected_target': None, 'chain': [str(p.relative_to(ROOT)) for p in chain]}
            (OUT / 'selection.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
            print(json.dumps(payload, indent=2))
            return 70
        verified = []
        selected = None
        for path in chain:
            result = verify_target(path, 2)
            verified.append(result)
            if not result['pass']:
                selected = str(path.relative_to(ROOT))
                break
        payload = {
            'all_pass': selected is None,
            'selected_target': selected,
            'chain': [str(p.relative_to(ROOT)) for p in chain],
            'verified': verified,
        }
        (OUT / 'selection.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
        print(json.dumps(payload, indent=2))
        return 0 if selected is None else 1

    if not args.target:
        raise SystemExit('--target is required')
    target = (ROOT / args.target).resolve()
    if args.mode == 'prepare':
        records = prepare_prerequisites(target)
        payload = {'target': args.target, 'prerequisites': records}
        (OUT / 'prerequisites.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
        print(json.dumps(payload, indent=2))
        return 0

    prepare_prerequisites(target)
    result = verify_target(target, args.runs)
    (OUT / 'target-verification.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result, indent=2))
    return 0 if result['pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
