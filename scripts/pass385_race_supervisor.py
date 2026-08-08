from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

import lean_repair_loop_v377 as guard
import priority_chain_v378 as chain

OUT = Path('/tmp/pass385-race-supervisor')
OUT.mkdir(parents=True, exist_ok=True)
TARGET = ROOT / 'PrimalitySheafVerification' / 'Mock2_FunctionalAnalysis.lean'
BRANCH = os.environ.get('SUPERVISOR_BRANCH', 'fix/fa385-race-supervisor-20260809')
CANDIDATES = [
    'fix/fa377-llm-loop-20260809',
    'fix/fa378-priority-beam-loop-20260809',
    'fix/fa379-blocking-priority-loop-20260809',
    'fix/fa380-blocking-cli-loop-20260809',
    'fix/fa381-instance-exhaustive-20260809',
    'fix/fa382-global-instance-probe-20260809',
    'fix/fa384-declaration-loop-20260809',
]


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ['git', *args], cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=check
    )


def fetch(branch: str) -> bool:
    proc = git(
        'fetch', '--no-tags', '--depth=2000', 'origin',
        f'+refs/heads/{branch}:refs/remotes/origin/{branch}', check=False
    )
    return proc.returncode == 0


def show_text(branch: str, path: str) -> str | None:
    proc = git('show', f'origin/{branch}:{path}', check=False)
    return proc.stdout if proc.returncode == 0 else None


def sha_text(text: str) -> str:
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def metrics(result: dict[str, Any], delta: int = 0) -> dict[str, Any]:
    line = result.get('first_error_line')
    adjusted = line - max(delta, 0) if isinstance(line, int) else None
    return {
        'exit_code': result['exit_code'],
        'artifacts_ok': result['artifacts_ok'],
        'error_headers': result['error_headers'],
        'first_error_line': line,
        'adjusted_first_error_line': adjusted,
        'first_error_message': result.get('first_error_message', ''),
        'source_sha256': result.get('source_sha256'),
        'log': result.get('log'),
    }


def better(a: dict[str, Any], b: dict[str, Any]) -> bool:
    if a['exit_code'] == 0 and a['artifacts_ok']:
        return not (b['exit_code'] == 0 and b['artifacts_ok'])
    if b['exit_code'] == 0 and b['artifacts_ok']:
        return False
    if a['error_headers'] != b['error_headers']:
        return a['error_headers'] < b['error_headers']
    x, y = a.get('adjusted_first_error_line'), b.get('adjusted_first_error_line')
    if isinstance(x, int) and isinstance(y, int):
        return x > y
    return False


def branch_priority_paths(branch: str) -> list[str]:
    fixed = [
        'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean',
        'PrimalitySheafVerification/Mock2_FunctionalAnalysis_Integrated.lean',
    ]
    tree = git('ls-tree', '-r', '--name-only', f'origin/{branch}', 'PrimalitySheafVerification', check=False)
    if tree.returncode == 0:
        for path in sorted(tree.stdout.splitlines()):
            name = Path(path).name.lower()
            if re.fullmatch(r'Mock3.*\.lean', Path(path).name) and not any(
                token in name for token in ('backup', 'candidate', 'probe', 'tmp')
            ):
                fixed.append(path)
    fixed.append('PrimalitySheafVerification/QYM.lean')
    return fixed


def copy_branch_sources(branch: str) -> list[Path]:
    copied = []
    for rel in branch_priority_paths(branch):
        text = show_text(branch, rel)
        if text is None:
            continue
        dst = ROOT / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(text, encoding='utf-8')
        copied.append(dst)
    return copied


def main() -> int:
    baseline = TARGET.read_text(encoding='utf-8')
    baseline_headers = guard.declaration_headers(baseline)
    baseline_imports = guard.imports(baseline)
    if guard.forbidden_hits(baseline):
        raise SystemExit('supervisor baseline contains forbidden executable token(s)')
    baseline_lines = len(baseline.splitlines())
    baseline_result = chain.compile_one(TARGET, 'race-baseline', max_errors=120)
    baseline_metrics = metrics(baseline_result)
    rows = [{
        'branch': BRANCH,
        'head': git('rev-parse', 'HEAD').stdout.strip(),
        'accepted': True,
        'metrics': baseline_metrics,
        'source_sha256': sha_text(baseline),
    }]
    best_branch = BRANCH
    best_source = baseline
    best_metrics = baseline_metrics

    for branch in CANDIDATES:
        if not fetch(branch):
            rows.append({'branch': branch, 'accepted': False, 'reason': 'fetch failed'})
            continue
        source = show_text(branch, 'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean')
        if source is None or len(source.encode('utf-8')) < 500000:
            rows.append({'branch': branch, 'accepted': False, 'reason': 'missing or stub FA source'})
            continue
        accepted = True
        reason = ''
        if guard.declaration_headers(source) != baseline_headers:
            accepted = False
            reason = 'public declaration header fingerprint differs from baseline'
        elif not baseline_imports.issubset(guard.imports(source)):
            accepted = False
            reason = 'existing import removed'
        elif guard.forbidden_hits(source):
            accepted = False
            reason = f'forbidden token(s): {guard.forbidden_hits(source)}'
        if accepted:
            TARGET.write_text(source, encoding='utf-8')
            result = chain.compile_one(TARGET, f'race-{branch.replace("/", "-")}', max_errors=120)
            row_metrics = metrics(result, len(source.splitlines()) - baseline_lines)
        else:
            row_metrics = {
                'exit_code': 999,
                'artifacts_ok': False,
                'error_headers': 10**9,
                'first_error_line': None,
                'adjusted_first_error_line': None,
                'first_error_message': reason,
                'source_sha256': sha_text(source),
                'log': None,
            }
        head = git('rev-parse', f'origin/{branch}').stdout.strip()
        row = {
            'branch': branch,
            'head': head,
            'accepted': accepted,
            'reason': reason,
            'metrics': row_metrics,
            'source_sha256': sha_text(source),
        }
        rows.append(row)
        if accepted and better(row_metrics, best_metrics):
            best_branch = branch
            best_source = source
            best_metrics = row_metrics
        TARGET.write_text(baseline, encoding='utf-8')

    copied: list[Path] = []
    if best_branch == BRANCH:
        TARGET.write_text(baseline, encoding='utf-8')
    else:
        copied = copy_branch_sources(best_branch)
        # The selected branch's FA source must equal the source actually ranked.
        if TARGET.read_text(encoding='utf-8') != best_source:
            raise SystemExit('selected branch changed between ranking and source copy')

    payload = {
        'baseline_branch': BRANCH,
        'baseline_metrics': baseline_metrics,
        'candidate_rows': rows,
        'best_branch': best_branch,
        'best_metrics': best_metrics,
        'copied_paths': [str(p.relative_to(ROOT)) for p in copied],
        'objectively_better_than_baseline': best_branch != BRANCH,
    }
    summary = ROOT / 'build-logs' / 'PASS385_RACE_SELECTION.json'
    summary.parent.mkdir(exist_ok=True)
    summary.write_text(json.dumps(payload, indent=2), encoding='utf-8')
    (OUT / 'summary.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
    print(json.dumps(payload, indent=2))

    git('config', 'user.name', 'github-actions[bot]')
    git('config', 'user.email', '41898282+github-actions[bot]@users.noreply.github.com')
    git('add', str(summary.relative_to(ROOT)))
    for path in copied:
        git('add', str(path.relative_to(ROOT)))
    if git('diff', '--cached', '--quiet', check=False).returncode != 0:
        git('commit', '-m', f'fix: select leading FA repair branch {best_branch}')
        push = git('push', 'origin', f'HEAD:{BRANCH}', check=False)
        if push.returncode != 0:
            raise RuntimeError('failed to push selected race candidate:\n' + push.stdout)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
