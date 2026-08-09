from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, asdict

ROOT = Path.cwd()
SRC = ROOT / 'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
OLEAN_DIR = ROOT / '.lake/build/lib/lean/PrimalitySheafVerification'
EVIDENCE = ROOT / 'build-logs/fa412-strict-champion-replay'
FULL_LOGS = EVIDENCE / 'full-logs'
EXPECTED_SHA = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
BASELINE_FIRST_ERROR = 31725
MAX_CANDIDATE_COMPILES = 24
SINCE = '2026-08-07T00:00:00Z'

ERROR_RE = re.compile(
    r'Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+'
    r'(?:error(?:\([^)]*\))?:|error:)')
HEX64_RE = re.compile(r'(?<![0-9a-f])[0-9a-f]{64}(?![0-9a-f])')
PROHIBITED_ADDITION_RE = re.compile(
    r'\b(?:sorry|admit|native_decide|unsafe|axiom)\b')


@dataclass
class Metric:
    exit_code: int
    first_error_line: int
    first_error_col: int
    captured_errors: int
    olean: bool
    ilean: bool

    @property
    def passed(self) -> bool:
        return self.exit_code == 0 and self.olean and self.ilean

    @property
    def score(self) -> tuple[int, int]:
        return (1, 10**12) if self.passed else (0, self.first_error_line)


@dataclass
class CandidateRecord:
    round: int
    script_blob: str
    script_origin: str
    input_sha256: str
    output_sha256: str
    script_exit: int
    audit_ok: bool
    compiled: bool
    metric: Metric | None
    promoted_in_round: bool
    reason: str


def run(cmd: list[str], *, check: bool = False, capture: bool = True,
        cwd: Path = ROOT) -> subprocess.CompletedProcess[str]:
    p = subprocess.run(
        cmd,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
    )
    if check and p.returncode != 0:
        raise RuntimeError(
            f"command failed ({p.returncode}): {' '.join(cmd)}\n{p.stdout or ''}")
    return p


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def compile_module(stem: str, log_path: Path, max_errors: int) -> Metric:
    OLEAN_DIR.mkdir(parents=True, exist_ok=True)
    src = ROOT / f'PrimalitySheafVerification/{stem}.lean'
    olean = OLEAN_DIR / f'{stem}.olean'
    ilean = OLEAN_DIR / f'{stem}.ilean'
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    cmd = [
        'lake', 'env', 'lean',
        f'-DmaxErrors={max_errors}',
        '-DwarningAsError=false',
        '-o', str(olean), '-i', str(ilean), str(src),
    ]
    with log_path.open('w', encoding='utf-8') as out:
        p = subprocess.run(cmd, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
    text = log_path.read_text(encoding='utf-8', errors='replace')
    ms = list(ERROR_RE.finditer(text)) if stem == 'Mock2_FunctionalAnalysis' else []
    return Metric(
        exit_code=p.returncode,
        first_error_line=int(ms[0].group(1)) if ms else 0,
        first_error_col=int(ms[0].group(2)) if ms else 0,
        captured_errors=len(ms),
        olean=olean.exists() and olean.stat().st_size > 0,
        ilean=ilean.exists() and ilean.stat().st_size > 0,
    )


def added_lines(old: bytes, new: bytes) -> list[str]:
    import difflib
    a = old.decode('utf-8', errors='replace').splitlines()
    b = new.decode('utf-8', errors='replace').splitlines()
    return [
        line[1:] for line in difflib.unified_diff(a, b, lineterm='')
        if line.startswith('+') and not line.startswith('+++')
    ]


def audit_candidate(old: bytes, new: bytes) -> tuple[bool, str]:
    if old == new:
        return False, 'script produced no source change'
    additions = added_lines(old, new)
    bad = [line for line in additions if PROHIBITED_ADDITION_RE.search(line)]
    if bad:
        return False, 'prohibited additions: ' + ' | '.join(bad[:8])
    return True, 'proof-bypass token audit passed'


def discover_scripts() -> list[dict[str, str]]:
    run([
        'git', 'fetch', '--no-tags', '--prune', 'origin',
        '+refs/heads/*:refs/remotes/origin/*'
    ], check=True)
    commits = run([
        'git', 'rev-list', '--all', f'--since={SINCE}', '--', 'scripts'
    ], check=True).stdout.splitlines()
    seen_blobs: set[str] = set()
    found: list[dict[str, str]] = []
    for commit in commits:
        changed = run([
            'git', 'diff-tree', '--no-commit-id', '--name-only', '-r', commit,
            '--', 'scripts'
        ], check=False).stdout.splitlines()
        for path in changed:
            if not re.fullmatch(r'scripts/fa\d+[^/]*\.py', path):
                continue
            blob_p = run(['git', 'rev-parse', f'{commit}:{path}'], check=False)
            if blob_p.returncode != 0:
                continue
            blob = blob_p.stdout.strip()
            if not blob or blob in seen_blobs:
                continue
            content_p = run(['git', 'cat-file', 'blob', blob], check=False)
            if content_p.returncode != 0:
                continue
            content = content_p.stdout
            seen_blobs.add(blob)
            found.append({
                'blob': blob,
                'origin': f'{commit}:{path}',
                'content': content,
                'content_sha256': hashlib.sha256(content.encode()).hexdigest(),
                'mentioned_hashes': sorted(set(HEX64_RE.findall(content))),
            })
    return found


def metric_str(m: Metric | None) -> str:
    if m is None:
        return 'not-compiled'
    if m.passed:
        return 'PASS'
    return f'{m.first_error_line}:{m.first_error_col}/exit={m.exit_code}'


def compact_log(full: Path, target: Path, metric: Metric) -> None:
    text = full.read_text(encoding='utf-8', errors='replace')
    if metric.passed:
        target.write_text(text[-12000:], encoding='utf-8')
        return
    ms = list(ERROR_RE.finditer(text))
    if not ms:
        target.write_text(text[:20000], encoding='utf-8')
        return
    start = max(0, ms[0].start() - 1000)
    end = min(len(text), ms[min(len(ms), 12) - 1].start() + 4000)
    target.write_text(text[start:end], encoding='utf-8')


def main() -> int:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    FULL_LOGS.mkdir(parents=True, exist_ok=True)
    baseline = SRC.read_bytes()
    baseline_sha = sha(baseline)
    if baseline_sha != EXPECTED_SHA:
        raise SystemExit(
            f'refusing replay: source {baseline_sha} != champion {EXPECTED_SHA}')
    marker = ROOT / 'build-logs/fa-pass376-champion-reproduction/REPRODUCED_31725_OR_BETTER'
    if not marker.exists():
        raise SystemExit('verified 31725 reproduction marker is missing')

    prereq = {}
    for stem in ('Mock2', 'Mock2_Advanced'):
        m = compile_module(stem, FULL_LOGS / f'{stem}.log', 500)
        prereq[stem] = asdict(m)
        if not m.passed:
            (EVIDENCE / 'RESULT.json').write_text(json.dumps({
                'complete': False,
                'stage': 'prerequisite failure',
                'prerequisites': prereq,
            }, indent=2) + '\n')
            return 30

    scripts = discover_scripts()
    manifest = [{k: v for k, v in s.items() if k != 'content'} for s in scripts]
    (EVIDENCE / 'DISCOVERED_SCRIPTS.json').write_text(
        json.dumps(manifest, indent=2) + '\n', encoding='utf-8')

    current = baseline
    current_sha = baseline_sha
    current_metric = Metric(1, BASELINE_FIRST_ERROR, 0, 0, False, False)
    initial_metric = current_metric
    records: list[CandidateRecord] = []
    accepted_chain: list[dict[str, object]] = []
    compile_count = 0
    round_no = 0

    while compile_count < MAX_CANDIDATE_COMPILES and not current_metric.passed:
        round_no += 1
        applicable = [s for s in scripts if current_sha in s['mentioned_hashes']]
        if not applicable:
            break
        best_bytes: bytes | None = None
        best_metric: Metric | None = None
        best_script: dict[str, str] | None = None
        best_record_index: int | None = None

        for index, script in enumerate(applicable, 1):
            if compile_count >= MAX_CANDIDATE_COMPILES:
                break
            SRC.write_bytes(current)
            script_path = Path('/tmp') / f"fa412-{round_no}-{index}-{script['blob'][:12]}.py"
            script_path.write_text(script['content'], encoding='utf-8')
            p = run([sys.executable, str(script_path)], check=False)
            script_output = p.stdout or ''
            (FULL_LOGS / f'round{round_no:02d}-candidate{index:02d}-script.log').write_text(
                script_output, encoding='utf-8')
            if p.returncode != 0:
                records.append(CandidateRecord(
                    round_no, script['blob'], script['origin'], current_sha,
                    current_sha, p.returncode, False, False, None, False,
                    'repair script rejected or failed'))
                run(['git', 'reset', '--hard', 'HEAD'], check=True)
                SRC.write_bytes(current)
                continue

            candidate = SRC.read_bytes()
            candidate_sha = sha(candidate)
            ok, audit_reason = audit_candidate(current, candidate)
            run(['git', 'reset', '--hard', 'HEAD'], check=True)
            SRC.write_bytes(candidate)
            if not ok:
                records.append(CandidateRecord(
                    round_no, script['blob'], script['origin'], current_sha,
                    candidate_sha, p.returncode, False, False, None, False,
                    audit_reason))
                SRC.write_bytes(current)
                continue

            compile_count += 1
            full_log = FULL_LOGS / (
                f'round{round_no:02d}-candidate{index:02d}-{candidate_sha[:12]}.log')
            metric = compile_module('Mock2_FunctionalAnalysis', full_log, 1200)
            compact_log(
                full_log,
                EVIDENCE / f'round{round_no:02d}-candidate{index:02d}-{candidate_sha[:12]}.context.txt',
                metric)
            strictly_better = metric.passed or (
                not current_metric.passed
                and metric.first_error_line > current_metric.first_error_line
            )
            reason = (
                f'strict improvement {metric_str(current_metric)} -> {metric_str(metric)}'
                if strictly_better else
                f'not strictly better than {metric_str(current_metric)}')
            records.append(CandidateRecord(
                round_no, script['blob'], script['origin'], current_sha,
                candidate_sha, p.returncode, True, True, metric, False, reason))
            rec_index = len(records) - 1
            if strictly_better and (
                best_metric is None or metric.score > best_metric.score
            ):
                best_bytes = candidate
                best_metric = metric
                best_script = script
                best_record_index = rec_index
            SRC.write_bytes(current)

        if best_bytes is None or best_metric is None or best_script is None:
            break
        records[best_record_index].promoted_in_round = True  # type: ignore[index]
        accepted_chain.append({
            'round': round_no,
            'script_blob': best_script['blob'],
            'script_origin': best_script['origin'],
            'input_sha256': current_sha,
            'output_sha256': sha(best_bytes),
            'old_metric': asdict(current_metric),
            'new_metric': asdict(best_metric),
        })
        current = best_bytes
        current_sha = sha(current)
        current_metric = best_metric

    SRC.write_bytes(baseline)
    (EVIDENCE / 'PROMOTED_SOURCE.lean').write_bytes(current)
    (EVIDENCE / 'CANDIDATES.json').write_text(
        json.dumps([
            {**asdict(r), 'metric': asdict(r.metric) if r.metric else None}
            for r in records
        ], indent=2) + '\n', encoding='utf-8')
    improved = current_metric.passed or (
        current_metric.first_error_line > BASELINE_FIRST_ERROR)
    result = {
        'complete': True,
        'baseline_sha256': baseline_sha,
        'baseline_first_error_line': BASELINE_FIRST_ERROR,
        'final_sha256': current_sha,
        'final_metric': asdict(current_metric),
        'final_passed': current_metric.passed,
        'strictly_improved': improved,
        'candidate_compiles': compile_count,
        'rounds': round_no,
        'accepted_chain': accepted_chain,
        'prerequisites': prereq,
        'promotion_policy': {
            'exit_zero_promotes': True,
            'nonzero_requires_strictly_larger_first_error': True,
            'regressions_never_replace_source_baseline': True,
            'prohibited_added_tokens': [
                'sorry', 'admit', 'native_decide', 'unsafe', 'axiom'
            ],
        },
    }
    (EVIDENCE / 'RESULT.json').write_text(
        json.dumps(result, indent=2) + '\n', encoding='utf-8')
    (EVIDENCE / 'RESULT.txt').write_text(
        f"baseline_sha256={baseline_sha}\n"
        f"baseline_first_error={BASELINE_FIRST_ERROR}\n"
        f"final_sha256={current_sha}\n"
        f"final_exit={current_metric.exit_code}\n"
        f"final_first_error={current_metric.first_error_line}:{current_metric.first_error_col}\n"
        f"final_passed={current_metric.passed}\n"
        f"strictly_improved={improved}\n"
        f"candidate_compiles={compile_count}\n"
        f"rounds={round_no}\n",
        encoding='utf-8')
    print((EVIDENCE / 'RESULT.txt').read_text())
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
