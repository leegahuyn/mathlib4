from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
OUT = Path('/tmp/pass383-marker-watcher')
OUT.mkdir(parents=True, exist_ok=True)
PR9_BRANCH = 'ci/fa319-isolated-20260807'
WATCHER_BRANCH = 'fix/fa383-marker-watcher-20260809'
MARKER = 'build-logs/FA_MOCK3_QYM_2X_PASS.json'
BRANCHES = [
    'fix/fa377-llm-loop-20260809',
    'fix/fa378-priority-beam-loop-20260809',
    'fix/fa379-blocking-priority-loop-20260809',
    'fix/fa380-blocking-cli-loop-20260809',
    'fix/fa381-instance-exhaustive-20260809',
    'fix/fa382-global-instance-probe-20260809',
]
WATCH_SECONDS = int(os.environ.get('WATCH_SECONDS', '19000'))
POLL_SECONDS = int(os.environ.get('POLL_SECONDS', '60'))

FORBIDDEN = [
    r'\bsorry\b', r'\badmit\b', r'^\s*axiom\b', r'\bunsafe\b',
    r'\bnative_decide\b', r'\bLean\.ofReduceBool\b',
]


def run(args: list[str], cwd: Path = ROOT, check: bool = True, timeout: int | None = None) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False, timeout=timeout,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(f"command failed ({proc.returncode}): {' '.join(args)}\n{proc.stdout}")
    return proc


def git(*args: str, cwd: Path = ROOT, check: bool = True) -> subprocess.CompletedProcess[str]:
    return run(['git', *args], cwd=cwd, check=check, timeout=600)


def fetch_branch(branch: str) -> bool:
    proc = git(
        'fetch', '--no-tags', '--prune', '--depth=2000', 'origin',
        f'+refs/heads/{branch}:refs/remotes/origin/{branch}', check=False,
    )
    return proc.returncode == 0


def branch_has_marker(branch: str) -> bool:
    proc = git('cat-file', '-e', f'origin/{branch}:{MARKER}', check=False)
    return proc.returncode == 0


def targets(root: Path) -> list[Path]:
    base = root / 'PrimalitySheafVerification'
    result = [
        base / 'Mock2_FunctionalAnalysis.lean',
        base / 'Mock2_FunctionalAnalysis_Integrated.lean',
    ]
    result.extend(sorted(
        p for p in base.glob('Mock3*.lean')
        if not any(x in p.name.lower() for x in ('backup', 'candidate', 'probe', 'tmp'))
    ))
    result.append(base / 'QYM.lean')
    return result


def artifact_paths(root: Path, source: Path) -> list[Path]:
    rel = source.relative_to(root).with_suffix('')
    base = root / '.lake' / 'build' / 'lib' / 'lean' / rel
    return [base.with_suffix('.olean'), base.with_suffix('.ilean')]


def compile_source(root: Path, source: Path, label: str) -> dict[str, Any]:
    for artifact in artifact_paths(root, source):
        artifact.unlink(missing_ok=True)
    log = OUT / f'{root.name}-{source.stem}-{label}.log'
    env = os.environ.copy()
    env['PATH'] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    proc = subprocess.run(
        ['lake', 'env', 'lean', '-DmaxErrors=300', str(source.relative_to(root))],
        cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False, timeout=1800,
    )
    log.write_text(proc.stdout, encoding='utf-8')
    errors = list(re.finditer(r'^.*?\.lean:(\d+):(\d+): error:\s*(.*)$', proc.stdout, re.M))
    artifacts_ok = proc.returncode == 0 and all(
        p.exists() and p.stat().st_size > 0 for p in artifact_paths(root, source)
    )
    return {
        'path': str(source.relative_to(root)),
        'exit_code': proc.returncode,
        'error_headers': len(errors),
        'first_error_line': int(errors[0].group(1)) if errors else None,
        'first_error_message': errors[0].group(3).strip() if errors else '',
        'artifacts_ok': artifacts_ok,
        'log': str(log),
    }


def strip_comments_strings(text: str) -> str:
    text = re.sub(r'/\*.*?\*/', '', text, flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    text = re.sub(r'"(?:\\.|[^"\\])*"', '""', text)
    return text


def trust_audit(files: list[Path]) -> dict[str, Any]:
    violations: dict[str, list[str]] = {}
    for path in files:
        text = strip_comments_strings(path.read_text(encoding='utf-8'))
        hits = [pat for pat in FORBIDDEN if re.search(pat, text, re.M)]
        if hits:
            violations[str(path)] = hits
    return {'pass': not violations, 'violations': violations}


def verify_two_rounds(root: Path) -> dict[str, Any]:
    chain = targets(root)
    missing = [str(p.relative_to(root)) for p in chain if not p.exists()]
    if missing:
        return {'pass': False, 'missing': missing, 'rounds': []}
    rounds = []
    for round_no in (1, 2):
        for source in chain:
            for artifact in artifact_paths(root, source):
                artifact.unlink(missing_ok=True)
        records = []
        for source in chain:
            record = compile_source(root, source, f'round-{round_no}')
            records.append(record)
            if record['exit_code'] != 0 or not record['artifacts_ok']:
                return {'pass': False, 'rounds': rounds + [{'round': round_no, 'records': records}]}
        rounds.append({'round': round_no, 'records': records})
    audit = trust_audit(chain)
    return {'pass': audit['pass'], 'rounds': rounds, 'trust': audit}


def worktree(path: Path, ref: str) -> None:
    if path.exists():
        git('worktree', 'remove', '--force', str(path), check=False)
        shutil.rmtree(path, ignore_errors=True)
    git('worktree', 'add', '--detach', str(path), ref)
    lake = path / '.lake'
    if lake.exists() or lake.is_symlink():
        if lake.is_dir() and not lake.is_symlink():
            shutil.rmtree(lake)
        else:
            lake.unlink()
    lake.symlink_to(ROOT / '.lake', target_is_directory=True)


def source_hashes(files: list[Path], root: Path) -> dict[str, str]:
    return {
        str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in files
    }


def copy_priority_sources(src_root: Path, dst_root: Path) -> list[Path]:
    src_files = targets(src_root)
    dst_base = dst_root / 'PrimalitySheafVerification'
    copied = []
    for src in src_files:
        dst = dst_base / src.name
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        copied.append(dst)
    return copied


def promote(winner: str, winner_root: Path, winner_verification: dict[str, Any]) -> dict[str, Any]:
    if not fetch_branch(PR9_BRANCH):
        raise RuntimeError(f'cannot fetch PR9 branch {PR9_BRANCH}')
    expected_head = git('rev-parse', f'origin/{PR9_BRANCH}').stdout.strip()
    pr9 = Path('/tmp/pass383-pr9')
    worktree(pr9, f'origin/{PR9_BRANCH}')
    copied = copy_priority_sources(winner_root, pr9)
    verification = verify_two_rounds(pr9)
    if not verification['pass']:
        return {
            'pass': False,
            'winner': winner,
            'reason': 'sources failed when applied to latest PR9 head',
            'expected_pr9_head': expected_head,
            'pr9_verification': verification,
        }
    if not fetch_branch(PR9_BRANCH):
        raise RuntimeError('cannot refresh PR9 head before push')
    current_head = git('rev-parse', f'origin/{PR9_BRANCH}').stdout.strip()
    if current_head != expected_head:
        return {
            'pass': False,
            'winner': winner,
            'reason': 'PR9 head changed during verification; refusing stale push',
            'expected_pr9_head': expected_head,
            'current_pr9_head': current_head,
        }
    marker = pr9 / MARKER
    marker.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        'status': 'SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS',
        'winner_branch': winner,
        'winner_head': git('rev-parse', f'origin/{winner}').stdout.strip(),
        'pr9_previous_head': expected_head,
        'source_hashes': source_hashes(copied, pr9),
        'winner_verification': winner_verification,
        'pr9_verification': verification,
        'draft_preserved': True,
        'automatic_merge': False,
    }
    marker.write_text(json.dumps(payload, indent=2), encoding='utf-8')
    git('config', 'user.name', 'github-actions[bot]', cwd=pr9)
    git('config', 'user.email', '41898282+github-actions[bot]@users.noreply.github.com', cwd=pr9)
    git('add', '--', *(str(p.relative_to(pr9)) for p in copied), MARKER, cwd=pr9)
    if git('diff', '--cached', '--quiet', cwd=pr9, check=False).returncode != 0:
        git('commit', '-m', 'fix: promote verified FA Integrated Mock3 QYM two-pass sources', cwd=pr9)
        push = git('push', 'origin', f'HEAD:{PR9_BRANCH}', cwd=pr9, check=False)
        if push.returncode != 0:
            raise RuntimeError('verified PR9 push failed:\n' + push.stdout)
    payload['pr9_new_head'] = git('rev-parse', 'HEAD', cwd=pr9).stdout.strip()
    return {'pass': True, 'promotion': payload}


def main() -> int:
    deadline = time.monotonic() + WATCH_SECONDS
    observed: dict[str, str] = {}
    events: list[dict[str, Any]] = []
    while time.monotonic() < deadline:
        for branch in BRANCHES:
            if not fetch_branch(branch):
                continue
            head = git('rev-parse', f'origin/{branch}').stdout.strip()
            if observed.get(branch) != head:
                observed[branch] = head
                events.append({'branch': branch, 'head': head, 'marker': branch_has_marker(branch)})
                (OUT / 'observed.json').write_text(json.dumps(events, indent=2), encoding='utf-8')
            if not branch_has_marker(branch):
                continue
            winner_root = Path('/tmp/pass383-winner')
            worktree(winner_root, f'origin/{branch}')
            verification = verify_two_rounds(winner_root)
            event = {'branch': branch, 'head': head, 'independent_verification': verification}
            events.append(event)
            (OUT / 'observed.json').write_text(json.dumps(events, indent=2), encoding='utf-8')
            if not verification['pass']:
                continue
            promotion = promote(branch, winner_root, verification)
            events.append({'promotion_attempt': promotion})
            (OUT / 'observed.json').write_text(json.dumps(events, indent=2), encoding='utf-8')
            if promotion['pass']:
                success = promotion['promotion']
                success_path = OUT / 'SUCCESS.json'
                success_path.write_text(json.dumps(success, indent=2), encoding='utf-8')
                local_marker = ROOT / 'build-logs' / 'PASS383_PROMOTED_TO_PR9.json'
                local_marker.parent.mkdir(exist_ok=True)
                local_marker.write_text(json.dumps(success, indent=2), encoding='utf-8')
                git('config', 'user.name', 'github-actions[bot]')
                git('config', 'user.email', '41898282+github-actions[bot]@users.noreply.github.com')
                git('add', str(local_marker.relative_to(ROOT)))
                if git('diff', '--cached', '--quiet', check=False).returncode != 0:
                    git('commit', '-m', 'ci: record verified priority-source promotion to PR9')
                    git('push', 'origin', f'HEAD:{WATCHER_BRANCH}')
                print(json.dumps(success, indent=2))
                return 0
        time.sleep(POLL_SECONDS)
    timeout = {
        'status': 'WATCH_DEADLINE_WITHOUT_VERIFIED_MARKER',
        'observed': observed,
        'events': events[-20:],
    }
    (OUT / 'TIMEOUT.json').write_text(json.dumps(timeout, indent=2), encoding='utf-8')
    print(json.dumps(timeout, indent=2))
    return 2


if __name__ == '__main__':
    raise SystemExit(main())
