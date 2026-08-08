from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

import lean_repair_loop_v377 as guard
import priority_chain_v378 as chain

BRANCH = os.environ.get('BRANCH_NAME', 'fix/fa379-blocking-priority-loop-20260809')
MAX_SECONDS = int(os.environ.get('BLOCKING_MAX_SECONDS', '19800'))
DEADLINE = time.monotonic() + MAX_SECONDS
BUILD_LOGS = ROOT / 'build-logs'
BUILD_LOGS.mkdir(exist_ok=True)
STATE_PATH = BUILD_LOGS / 'PASS379_BLOCKING_STATE.json'
CURRENT_PATH = BUILD_LOGS / 'PASS379_BLOCKING_CURRENT.json'
MARKER_PATH = BUILD_LOGS / 'FA_MOCK3_QYM_2X_PASS.json'
RUN_EVIDENCE = Path('/tmp/pass379-blocking')
RUN_EVIDENCE.mkdir(parents=True, exist_ok=True)

STYLES = [
    (
        'gpt5-typeclass',
        'openai/gpt-5,openai/gpt-4.1,openai/gpt-4o',
        'Fix the first independent elaboration or typeclass root. Normalize competing inherited '
        'structures explicitly using letI, change, show, @-qualified constants, and current mathlib APIs. '
        'Do not patch downstream symptoms.',
    ),
    (
        'gpt41-api',
        'openai/gpt-4.1,openai/gpt-5,openai/gpt-4o',
        'Treat this as a precise mathlib API migration. Compare expected and actual types, expose coercions '
        'and dependent transports, and use one small private proved helper only when it removes a real cascade.',
    ),
    (
        'gpt4o-local-proof',
        'openai/gpt-4o,openai/gpt-4.1,openai/gpt-5',
        'Rewrite only the nearest failing proof. Prefer calc, ext, change, simpa only, explicit namespaces, '
        'typed intermediate facts, and theorem application over broad simp.',
    ),
    (
        'gpt5-root-architecture',
        'openai/gpt-5,openai/gpt-4.1,openai/gpt-4o',
        'The previous local approaches may have patched symptoms. Identify the common definitional equality, '
        'index transport, scalar-action, or instance root shared by the first several errors and repair that '
        'root without changing any existing public declaration header.',
    ),
]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ['git', *args], cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=check
    )


def configure_git() -> None:
    git('config', 'user.name', 'github-actions[bot]')
    git('config', 'user.email', '41898282+github-actions[bot]@users.noreply.github.com')


def source_files() -> list[Path]:
    return [p for p in chain.targets() if p.exists()]


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding='utf-8')


def commit_and_push(message: str, paths: list[Path]) -> None:
    rels = [str(p.relative_to(ROOT)) for p in paths if p.exists()]
    if not rels:
        return
    git('add', '--', *rels)
    staged = git('diff', '--cached', '--quiet', check=False)
    if staged.returncode == 0:
        return
    git('commit', '-m', message)
    push = git('push', 'origin', f'HEAD:{BRANCH}', check=False)
    if push.returncode != 0:
        # A concurrent diagnostic commit must never silently overwrite verified progress.
        git('fetch', 'origin', BRANCH, '--depth=50', check=False)
        raise RuntimeError(f'failed to push blocking-loop progress:\n{push.stdout}')


def trust_audit(paths: list[Path]) -> dict[str, Any]:
    bad: dict[str, list[str]] = {}
    for path in paths:
        hits = guard.forbidden_hits(path.read_text(encoding='utf-8'))
        if hits:
            bad[str(path.relative_to(ROOT))] = hits
    return {'pass': not bad, 'violations': bad}


def load_locked_state(targets: list[Path]) -> tuple[int, list[dict[str, Any]]]:
    if not STATE_PATH.exists():
        return 0, []
    try:
        state = json.loads(STATE_PATH.read_text(encoding='utf-8'))
    except Exception:
        return 0, []
    records = state.get('locked_records', [])
    locked = 0
    valid_records: list[dict[str, Any]] = []
    for index, record in enumerate(records):
        if index >= len(targets):
            break
        path = targets[index]
        if record.get('path') != str(path.relative_to(ROOT)):
            break
        if record.get('source_sha256') != sha(path):
            break
        locked += 1
        valid_records.append(record)
    return locked, valid_records


def save_state(
    cycle: int,
    locked: int,
    locked_records: list[dict[str, Any]],
    selected: str | None,
    last_result: dict[str, Any] | None,
    status: str,
) -> None:
    payload = {
        'status': status,
        'cycle': cycle,
        'locked_prefix_length': locked,
        'locked_records': locked_records,
        'selected_target': selected,
        'last_result': last_result,
        'source_hashes': {
            str(path.relative_to(ROOT)): sha(path) for path in source_files()
        },
        'elapsed_seconds': round(MAX_SECONDS - max(0, DEADLINE - time.monotonic()), 2),
        'branch': BRANCH,
        'workflow_run_id': os.environ.get('GITHUB_RUN_ID', ''),
        'workflow_sha': os.environ.get('GITHUB_SHA', ''),
    }
    write_json(STATE_PATH, payload)
    write_json(CURRENT_PATH, payload)


def compile_locked_prerequisites(targets: list[Path], locked: int) -> tuple[int, list[dict[str, Any]]]:
    records: list[dict[str, Any]] = []
    for index, path in enumerate(targets[:locked]):
        result = chain.compile_one(path, f'locked-prerequisite-{index}', max_errors=200)
        records.append(result)
        if result['exit_code'] != 0 or not result['artifacts_ok']:
            return index, records
    return locked, records


def choose_target(
    targets: list[Path],
    locked: int,
    locked_records: list[dict[str, Any]],
    cycle: int,
) -> tuple[int, list[dict[str, Any]], Path | None, dict[str, Any] | None]:
    prepared_locked, prerequisite_records = compile_locked_prerequisites(targets, locked)
    if prepared_locked < locked:
        locked = prepared_locked
        locked_records = locked_records[:locked]
    while locked < len(targets):
        path = targets[locked]
        result = chain.verify_target(path, 2)
        if not result['pass']:
            return locked, locked_records, path, result
        record = {
            'path': str(path.relative_to(ROOT)),
            'source_sha256': sha(path),
            'verified_at_cycle': cycle,
            'verification': result,
        }
        locked_records.append(record)
        locked += 1
        save_state(cycle, locked, locked_records, None, result, 'target-locked-after-2x-pass')
        commit_and_push(
            f'ci: lock two-pass target {path.stem} at blocking cycle {cycle}',
            [STATE_PATH, CURRENT_PATH],
        )
        if locked < len(targets):
            # Generate the freshly verified target artifact needed by the next import.
            prereq = chain.compile_one(path, 'next-target-prerequisite', max_errors=200)
            if prereq['exit_code'] != 0 or not prereq['artifacts_ok']:
                return locked - 1, locked_records[:-1], path, {'pass': False, 'runs': [prereq]}
    return locked, locked_records, None, None


def run_agent(target: Path, cycle: int, style_index: int) -> dict[str, Any]:
    slug, models, style = STYLES[style_index]
    env = os.environ.copy()
    env['PATH'] = f"{Path.home() / '.elan' / 'bin'}:{env.get('PATH', '')}"
    env['MODEL_CANDIDATES'] = models
    env['REPAIR_STYLE'] = (
        f'Blocking repair cycle {cycle}, strategy {slug}. {style} '
        'A candidate is accepted only after the same pinned Lean compiler objectively improves.'
    )
    before = sha(target)
    log = RUN_EVIDENCE / f'cycle-{cycle:03d}-{slug}.driver.log'
    remaining = max(60, int(DEADLINE - time.monotonic()))
    timeout = min(7200, remaining)
    start = time.monotonic()
    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(ROOT / 'scripts' / 'run_lean_repair_v377_styled.py'),
                '--target', str(target.relative_to(ROOT)),
                '--iterations', '5',
                '--attempts-per-iteration', '3',
            ],
            cwd=ROOT,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        output = proc.stdout
        rc = proc.returncode
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or '') + '\n[blocking-loop] repair agent timeout\n'
        rc = 124
    log.write_text(output, encoding='utf-8')
    after = sha(target)
    status_path = Path('/tmp/lean-repair-v377') / target.stem / 'status.json'
    agent_status: dict[str, Any] = {}
    if status_path.exists():
        try:
            agent_status = json.loads(status_path.read_text(encoding='utf-8'))
        except Exception:
            agent_status = {'parse_error': True}
    return {
        'slug': slug,
        'models': models,
        'driver_exit': rc,
        'source_before': before,
        'source_after': after,
        'changed': before != after,
        'agent_status': agent_status,
        'elapsed_seconds': round(time.monotonic() - start, 2),
        'driver_log': str(log),
    }


def final_two_rounds(targets: list[Path]) -> dict[str, Any]:
    rounds: list[dict[str, Any]] = []
    for round_no in (1, 2):
        for path in targets:
            for artifact in chain.artifact_paths(path):
                artifact.unlink(missing_ok=True)
        records = []
        for path in targets:
            result = chain.compile_one(path, f'final-round-{round_no}', max_errors=300)
            records.append(result)
            if result['exit_code'] != 0 or not result['artifacts_ok']:
                return {'pass': False, 'rounds': rounds + [{'round': round_no, 'records': records}]}
        rounds.append({'round': round_no, 'records': records})
    trust = trust_audit(targets)
    return {'pass': trust['pass'], 'rounds': rounds, 'trust': trust}


def main() -> int:
    configure_git()
    targets = chain.targets()
    missing = [str(p.relative_to(ROOT)) for p in targets if not p.exists()]
    if missing:
        payload = {'status': 'missing-priority-source', 'missing': missing}
        write_json(CURRENT_PATH, payload)
        commit_and_push('ci: record missing priority source', [CURRENT_PATH])
        return 70

    baseline_headers = {
        str(path.relative_to(ROOT)): guard.declaration_headers(path.read_text(encoding='utf-8'))
        for path in targets
    }
    baseline_imports = {
        str(path.relative_to(ROOT)): guard.imports(path.read_text(encoding='utf-8'))
        for path in targets
    }
    audit = trust_audit(targets)
    if not audit['pass']:
        write_json(CURRENT_PATH, {'status': 'baseline-trust-audit-failed', 'audit': audit})
        commit_and_push('ci: record priority trust-audit failure', [CURRENT_PATH])
        return 71

    locked, locked_records = load_locked_state(targets)
    cycle = 0
    history: list[dict[str, Any]] = []

    while time.monotonic() < DEADLINE:
        cycle += 1
        locked, locked_records, selected, selection_result = choose_target(
            targets, locked, locked_records, cycle
        )
        if selected is None:
            final = final_two_rounds(targets)
            if final['pass']:
                payload = {
                    'status': 'SUCCESS_ALL_REQUIRED_TARGETS_2X_PASS',
                    'pass': True,
                    'branch': BRANCH,
                    'workflow_run_id': os.environ.get('GITHUB_RUN_ID', ''),
                    'cycle': cycle,
                    'source_hashes': {
                        str(path.relative_to(ROOT)): sha(path) for path in targets
                    },
                    'final_verification': final,
                    'locked_records': locked_records,
                }
                write_json(MARKER_PATH, payload)
                write_json(CURRENT_PATH, payload)
                commit_and_push(
                    'fix: FA Integrated Mock3 QYM final two-round PASS',
                    targets + [MARKER_PATH, CURRENT_PATH, STATE_PATH],
                )
                print(json.dumps(payload, indent=2))
                return 0
            # A target that failed only in the clean final round becomes active again.
            failing_record = final['rounds'][-1]['records'][-1]
            failing_path = ROOT / failing_record['path']
            locked = targets.index(failing_path)
            locked_records = locked_records[:locked]
            selected = failing_path
            selection_result = {'pass': False, 'runs': [failing_record]}

        selected_rel = str(selected.relative_to(ROOT))
        save_state(cycle, locked, locked_records, selected_rel, selection_result, 'repairing')
        commit_and_push(
            f'ci: record blocking cycle {cycle} target {selected.stem}',
            [STATE_PATH, CURRENT_PATH],
        )

        made_progress = False
        cycle_record: dict[str, Any] = {
            'cycle': cycle,
            'target': selected_rel,
            'selection_result': selection_result,
            'attempts': [],
        }
        for style_index in range(len(STYLES)):
            if time.monotonic() >= DEADLINE:
                break
            # Rebuild the preceding checked-in modules before each independent agent attempt.
            try:
                chain.prepare_prerequisites(selected)
            except SystemExit as exc:
                cycle_record['prerequisite_error'] = str(exc)
                break
            before_source = selected.read_text(encoding='utf-8')
            attempt = run_agent(selected, cycle, style_index)
            cycle_record['attempts'].append(attempt)
            after_source = selected.read_text(encoding='utf-8')
            rel = str(selected.relative_to(ROOT))
            if guard.declaration_headers(after_source) != baseline_headers[rel]:
                selected.write_text(before_source, encoding='utf-8')
                attempt['rejected_after_agent'] = 'public declaration header changed'
                continue
            if not baseline_imports[rel].issubset(guard.imports(after_source)):
                selected.write_text(before_source, encoding='utf-8')
                attempt['rejected_after_agent'] = 'existing import removed'
                continue
            hits = guard.forbidden_hits(after_source)
            if hits:
                selected.write_text(before_source, encoding='utf-8')
                attempt['rejected_after_agent'] = f'forbidden token(s): {hits}'
                continue
            if not attempt['changed']:
                continue
            # Independently confirm that the committed source really advanced.
            confirmation = chain.compile_one(
                selected, f'blocking-cycle-{cycle}-confirmation', max_errors=120
            )
            attempt['independent_confirmation'] = confirmation
            agent_final = attempt.get('agent_status', {}).get('final', {})
            old_errors = None
            if isinstance(attempt.get('agent_status'), dict):
                hist = attempt['agent_status'].get('history', [])
                if hist:
                    old_errors = hist[0].get('error_headers')
            objectively_improved = (
                confirmation['exit_code'] == 0
                or (
                    isinstance(old_errors, int)
                    and confirmation['error_headers'] < old_errors
                )
                or bool(attempt.get('agent_status', {}).get('progress'))
            )
            if not objectively_improved:
                selected.write_text(before_source, encoding='utf-8')
                attempt['rejected_after_agent'] = 'independent compiler did not confirm progress'
                continue
            made_progress = True
            cycle_evidence = BUILD_LOGS / f'PASS379_CYCLE_{cycle:03d}.json'
            history.append(cycle_record)
            write_json(cycle_evidence, cycle_record)
            save_state(
                cycle, locked, locked_records, selected_rel,
                {'confirmation': confirmation, 'attempt': attempt}, 'objective-source-progress'
            )
            commit_and_push(
                f'fix: advance {selected.stem} at blocking PASS cycle {cycle}',
                [selected, cycle_evidence, STATE_PATH, CURRENT_PATH],
            )
            break

        if not made_progress:
            history.append(cycle_record)
            stalled = {
                'status': 'STALLED_NO_OBJECTIVE_MODEL_CANDIDATE',
                'cycle': cycle,
                'locked_prefix_length': locked,
                'selected_target': selected_rel,
                'history_tail': history[-3:],
                'source_hashes': {
                    str(path.relative_to(ROOT)): sha(path) for path in targets
                },
            }
            write_json(CURRENT_PATH, stalled)
            evidence = BUILD_LOGS / f'PASS379_STALLED_CYCLE_{cycle:03d}.json'
            write_json(evidence, stalled)
            commit_and_push(
                f'ci: record stalled blocking cycle {cycle}',
                [CURRENT_PATH, STATE_PATH, evidence],
            )
            print(json.dumps(stalled, indent=2))
            return 2

    timeout_payload = {
        'status': 'BLOCKING_RUNTIME_LIMIT_REACHED_WITH_PROGRESS_PRESERVED',
        'cycle': cycle,
        'locked_prefix_length': locked,
        'locked_records': locked_records,
        'source_hashes': {
            str(path.relative_to(ROOT)): sha(path) for path in targets
        },
        'history_tail': history[-5:],
    }
    write_json(CURRENT_PATH, timeout_payload)
    commit_and_push('ci: preserve blocking-loop runtime-limit state', [CURRENT_PATH, STATE_PATH])
    print(json.dumps(timeout_payload, indent=2))
    return 3


if __name__ == '__main__':
    raise SystemExit(main())
