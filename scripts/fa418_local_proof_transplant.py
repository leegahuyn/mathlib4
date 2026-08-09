from __future__ import annotations

from dataclasses import asdict, dataclass
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path.cwd()
SRC = ROOT / 'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'
OLEAN_DIR = ROOT / '.lake/build/lib/lean/PrimalitySheafVerification'
OUT = ROOT / 'build-logs/fa418-local-proof-transplant'
LOGS = OUT / 'full-logs'
EXPECTED_SHA = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
REQUIRED_FRONTIER = 31725
MAX_COMPILES = 24
PATH = 'PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean'

ERROR_RE = re.compile(
    r'Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+'
    r'(?:error(?:\([^)]*\))?:|error:)')
DECL_RE = re.compile(
    r'^(?:(?:noncomputable|private|protected)\s+)*'
    r'(theorem|lemma|def|abbrev|instance)\s+([A-Za-z0-9_\u0080-\uffff\'.]+)')
BOUNDARY_RE = re.compile(
    r'^(?:@\[[^\n]*\]\s*)?'
    r'(?:(?:noncomputable|private|protected)\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|class|namespace|section|end)\b')
PROHIBITED_RE = re.compile(r'\b(?:sorry|admit|native_decide|unsafe|axiom)\b')


@dataclass
class Metric:
    exit_code: int
    first_error_line: int
    first_error_col: int
    errors: int
    olean: bool
    ilean: bool

    @property
    def passed(self) -> bool:
        return self.exit_code == 0 and self.olean and self.ilean

    @property
    def score(self) -> tuple[int, int]:
        return (1, 10**12) if self.passed else (0, self.first_error_line)


@dataclass
class Declaration:
    name: str
    kind: str
    start_line: int
    end_line_exclusive: int
    start_offset: int
    end_offset: int
    segment: str
    assign_start: int
    assign_end: int
    normalized_signature: str


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(args: list[str], *, check: bool = False) -> subprocess.CompletedProcess[str]:
    p = subprocess.run(
        args, cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if check and p.returncode != 0:
        raise RuntimeError(f"command failed: {' '.join(args)}\n{p.stdout}")
    return p


def compile_module(stem: str, log: Path, max_errors: int = 1400) -> Metric:
    OLEAN_DIR.mkdir(parents=True, exist_ok=True)
    source = ROOT / f'PrimalitySheafVerification/{stem}.lean'
    olean = OLEAN_DIR / f'{stem}.olean'
    ilean = OLEAN_DIR / f'{stem}.ilean'
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    with log.open('w', encoding='utf-8') as out:
        p = subprocess.run([
            'lake', 'env', 'lean', f'-DmaxErrors={max_errors}',
            '-DwarningAsError=false', '-o', str(olean), '-i', str(ilean),
            str(source)
        ], cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
    text = log.read_text(encoding='utf-8', errors='replace')
    ms = list(ERROR_RE.finditer(text)) if stem == 'Mock2_FunctionalAnalysis' else []
    return Metric(
        p.returncode,
        int(ms[0].group(1)) if ms else 0,
        int(ms[0].group(2)) if ms else 0,
        len(ms),
        olean.exists() and olean.stat().st_size > 0,
        ilean.exists() and ilean.stat().st_size > 0,
    )


def line_offsets(lines: list[str]) -> list[int]:
    result = [0]
    total = 0
    for line in lines:
        total += len(line)
        result.append(total)
    return result


def normalize_signature(text: str) -> str:
    text = re.sub(r'/\*.*?\*/', ' ', text, flags=re.S)
    text = re.sub(r'--[^\n]*', ' ', text)
    return re.sub(r'\s+', ' ', text).strip()


def parse_declarations(text: str) -> list[Declaration]:
    lines = text.splitlines(keepends=True)
    starts: list[tuple[int, str, str]] = []
    for i, line in enumerate(lines, 1):
        m = DECL_RE.match(line)
        if m:
            starts.append((i, m.group(1), m.group(2)))
    offsets = line_offsets(lines)
    declarations: list[Declaration] = []
    for start_line, kind, name in starts:
        end_line = len(lines) + 1
        for i in range(start_line + 1, len(lines) + 1):
            if BOUNDARY_RE.match(lines[i - 1]):
                end_line = i
                break
        start = offsets[start_line - 1]
        end = offsets[end_line - 1] if end_line <= len(lines) else len(text)
        segment = text[start:end]
        assignments = list(re.finditer(r':=\s*by\b', segment))
        if not assignments:
            continue
        a = assignments[-1]
        declarations.append(Declaration(
            name=name,
            kind=kind,
            start_line=start_line,
            end_line_exclusive=end_line,
            start_offset=start,
            end_offset=end,
            segment=segment,
            assign_start=a.start(),
            assign_end=a.end(),
            normalized_signature=normalize_signature(segment[:a.start() + 2]),
        ))
    return declarations


def enclosing_declaration(text: str, line: int) -> Declaration | None:
    for d in parse_declarations(text):
        if d.start_line <= line < d.end_line_exclusive:
            return d
    return None


def remove_full_line_comments_and_blanks(proof: str) -> str:
    lines = proof.splitlines(keepends=True)
    kept = []
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith('--'):
            continue
        kept.append(line)
    return ''.join(kept)


def transplant(current: str, current_decl: Declaration,
               donor_decl: Declaration) -> str | None:
    if current_decl.normalized_signature != donor_decl.normalized_signature:
        return None
    current_segment = current_decl.segment
    donor_segment = donor_decl.segment
    prefix = current_segment[:current_decl.assign_start + 2]
    donor_proof = donor_segment[donor_decl.assign_start + 2:]
    candidate_segment = prefix + donor_proof
    target_newlines = current_segment.count('\n')
    if candidate_segment.count('\n') > target_newlines:
        donor_proof = remove_full_line_comments_and_blanks(donor_proof)
        candidate_segment = prefix + donor_proof
    if candidate_segment.count('\n') > target_newlines:
        return None
    candidate_segment = candidate_segment.rstrip('\n') + '\n'
    candidate_segment += '\n' * (target_newlines - candidate_segment.count('\n'))
    if candidate_segment.count('\n') != target_newlines:
        return None
    return (
        current[:current_decl.start_offset] + candidate_segment +
        current[current_decl.end_offset:]
    )


def added_lines(old: str, new: str) -> list[str]:
    return [
        line[1:] for line in difflib.unified_diff(
            old.splitlines(), new.splitlines(), lineterm='')
        if line.startswith('+') and not line.startswith('+++')
    ]


def audit(old: str, new: str, declaration: Declaration) -> tuple[bool, str]:
    if old == new:
        return False, 'no source change'
    if len(old.splitlines()) != len(new.splitlines()):
        return False, 'line count changed'
    new_decl = enclosing_declaration(new, declaration.start_line)
    if new_decl is None:
        return False, 'declaration disappeared'
    if new_decl.name != declaration.name:
        return False, 'declaration identity changed'
    if new_decl.normalized_signature != declaration.normalized_signature:
        return False, 'declaration signature changed'
    bad = [line for line in added_lines(old, new) if PROHIBITED_RE.search(line)]
    if bad:
        return False, 'prohibited addition: ' + ' | '.join(bad[:5])
    return True, 'same signature, same line count, token audit clean'


def collect_versions() -> list[dict[str, str]]:
    run([
        'git', 'fetch', '--no-tags', '--prune', 'origin',
        '+refs/heads/*:refs/remotes/origin/*'
    ], check=True)
    commits = run([
        'git', 'rev-list', '--all', '--since=2026-08-07T00:00:00Z', '--', PATH
    ], check=True).stdout.splitlines()
    versions: list[dict[str, str]] = []
    seen: set[str] = set()
    for commit in commits:
        p = run(['git', 'show', f'{commit}:{PATH}'])
        if p.returncode != 0:
            continue
        content = p.stdout
        digest = hashlib.sha256(content.encode()).hexdigest()
        if digest in seen:
            continue
        seen.add(digest)
        versions.append({
            'origin': commit,
            'sha256': digest,
            'content': content,
        })
    return versions


def compact_log(source: Path, target: Path) -> None:
    text = source.read_text(encoding='utf-8', errors='replace')
    ms = list(ERROR_RE.finditer(text))
    if not ms:
        target.write_text(text[:20000], encoding='utf-8')
        return
    start = max(0, ms[0].start() - 700)
    end = min(len(text), ms[min(10, len(ms)) - 1].start() + 4000)
    target.write_text(text[start:end], encoding='utf-8')


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    baseline_bytes = SRC.read_bytes()
    baseline_sha = sha(baseline_bytes)
    if baseline_sha != EXPECTED_SHA:
        raise SystemExit(f'wrong baseline SHA: {baseline_sha}')

    prerequisites = {}
    for stem in ('Mock2', 'Mock2_Advanced'):
        m = compile_module(stem, LOGS / f'{stem}.log', 500)
        prerequisites[stem] = asdict(m)
        if not m.passed:
            raise SystemExit(f'prerequisite failed: {stem}')

    baseline_metric = compile_module(
        'Mock2_FunctionalAnalysis', LOGS / 'baseline.log', 1400)
    if not baseline_metric.passed and baseline_metric.first_error_line < REQUIRED_FRONTIER:
        raise SystemExit(
            f'baseline regression {baseline_metric.first_error_line} < {REQUIRED_FRONTIER}')

    versions = collect_versions()
    (OUT / 'VERSION_MANIFEST.json').write_text(json.dumps([
        {'origin': v['origin'], 'sha256': v['sha256']}
        for v in versions
    ], indent=2) + '\n', encoding='utf-8')

    current = baseline_bytes.decode('utf-8')
    current_sha = baseline_sha
    current_metric = baseline_metric
    records: list[dict[str, object]] = []
    accepted: list[dict[str, object]] = []
    compile_count = 0
    round_no = 0

    while not current_metric.passed and compile_count < MAX_COMPILES:
        round_no += 1
        declaration = enclosing_declaration(current, current_metric.first_error_line)
        if declaration is None:
            records.append({
                'round': round_no,
                'reason': 'first error is not inside a supported declaration',
                'first_error_line': current_metric.first_error_line,
            })
            break

        donor_candidates: list[tuple[str, str, str]] = []
        seen_sources: set[str] = set()
        for version in versions:
            donors = {
                d.name: d for d in parse_declarations(version['content'])
                if d.normalized_signature == declaration.normalized_signature
            }
            donor = donors.get(declaration.name)
            if donor is None:
                continue
            candidate = transplant(current, declaration, donor)
            if candidate is None:
                continue
            candidate_sha = hashlib.sha256(candidate.encode()).hexdigest()
            if candidate_sha in seen_sources or candidate_sha == current_sha:
                continue
            seen_sources.add(candidate_sha)
            donor_candidates.append((version['origin'], candidate_sha, candidate))

        if not donor_candidates:
            records.append({
                'round': round_no,
                'declaration': declaration.name,
                'reason': 'no same-signature donor proof found',
            })
            break

        best: tuple[str, str, str, Metric] | None = None
        for index, (origin, candidate_sha, candidate) in enumerate(donor_candidates, 1):
            if compile_count >= MAX_COMPILES:
                break
            ok, reason = audit(current, candidate, declaration)
            if not ok:
                records.append({
                    'round': round_no, 'declaration': declaration.name,
                    'origin': origin, 'candidate_sha256': candidate_sha,
                    'compiled': False, 'promoted': False, 'reason': reason,
                })
                continue
            SRC.write_text(candidate, encoding='utf-8')
            compile_count += 1
            log = LOGS / f'round{round_no:02d}-{index:02d}-{candidate_sha[:12]}.log'
            metric = compile_module('Mock2_FunctionalAnalysis', log, 1400)
            compact_log(log, OUT / f'round{round_no:02d}-{index:02d}.context.txt')
            strictly_better = metric.passed or (
                not current_metric.passed and
                metric.first_error_line > current_metric.first_error_line
            )
            records.append({
                'round': round_no, 'declaration': declaration.name,
                'origin': origin, 'input_sha256': current_sha,
                'candidate_sha256': candidate_sha, 'compiled': True,
                'metric': asdict(metric), 'promoted': False,
                'reason': 'strict improvement' if strictly_better else
                          f'not better than {current_metric.first_error_line}',
            })
            if strictly_better and (best is None or metric.score > best[3].score):
                best = (origin, candidate_sha, candidate, metric)
            SRC.write_text(current, encoding='utf-8')

        if best is None:
            break
        origin, current_sha, current, new_metric = best
        for record in reversed(records):
            if record.get('candidate_sha256') == current_sha:
                record['promoted'] = True
                break
        accepted.append({
            'round': round_no,
            'declaration': declaration.name,
            'donor_origin': origin,
            'sha256': current_sha,
            'old_metric': asdict(current_metric),
            'new_metric': asdict(new_metric),
        })
        current_metric = new_metric
        SRC.write_text(current, encoding='utf-8')

    SRC.write_bytes(baseline_bytes)
    (OUT / 'PROMOTED_SOURCE.lean').write_text(current, encoding='utf-8')
    improved = current_metric.passed or (
        current_metric.first_error_line > baseline_metric.first_error_line)
    result = {
        'complete': True,
        'baseline_sha256': baseline_sha,
        'baseline_metric': asdict(baseline_metric),
        'final_sha256': current_sha,
        'final_metric': asdict(current_metric),
        'strictly_improved': improved,
        'final_passed': current_metric.passed,
        'candidate_compiles': compile_count,
        'rounds': round_no,
        'accepted_chain': accepted,
        'candidate_records': records,
        'versions_scanned': len(versions),
        'prerequisites': prerequisites,
        'policy': {
            'whole_files_from_regressed_branches_never_used': True,
            'same_declaration_signature_required': True,
            'line_count_preserved': True,
            'nonzero_candidate_requires_strictly_later_first_error': True,
        },
    }
    (OUT / 'RESULT.json').write_text(
        json.dumps(result, indent=2) + '\n', encoding='utf-8')
    (OUT / 'RESULT.txt').write_text(
        f"baseline_sha256={baseline_sha}\n"
        f"baseline_first_error={baseline_metric.first_error_line}:{baseline_metric.first_error_col}\n"
        f"final_sha256={current_sha}\n"
        f"final_exit={current_metric.exit_code}\n"
        f"final_first_error={current_metric.first_error_line}:{current_metric.first_error_col}\n"
        f"final_passed={current_metric.passed}\n"
        f"strictly_improved={improved}\n"
        f"candidate_compiles={compile_count}\n"
        f"versions_scanned={len(versions)}\n",
        encoding='utf-8')
    print((OUT / 'RESULT.txt').read_text())
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
