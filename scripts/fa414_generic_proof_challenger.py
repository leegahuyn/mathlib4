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
OUT = ROOT / 'build-logs/fa414-generic-proof-challenger'
LOGS = OUT / 'full-logs'
EXPECTED_SHA = '07f6efd3309c3cc23b86adf5811918b752b72c33a3f7a76213ce9beb10796da4'
REQUIRED_FRONTIER = 31725
MAX_COMPILES = 18

ERROR_RE = re.compile(
    r'Mock2_FunctionalAnalysis\.lean:(\d+):(\d+):\s+'
    r'(?:error(?:\([^)]*\))?:|error:)')
DECL_START_RE = re.compile(
    r'^(?:@\[[^\n]*\]\s*)?'
    r'(?:(?:noncomputable|private|protected)\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance)\b')
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


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def compile_module(stem: str, log: Path, max_errors: int = 1200) -> Metric:
    OLEAN_DIR.mkdir(parents=True, exist_ok=True)
    source = ROOT / f'PrimalitySheafVerification/{stem}.lean'
    olean = OLEAN_DIR / f'{stem}.olean'
    ilean = OLEAN_DIR / f'{stem}.ilean'
    olean.unlink(missing_ok=True)
    ilean.unlink(missing_ok=True)
    with log.open('w', encoding='utf-8') as out:
        p = subprocess.run([
            'lake', 'env', 'lean',
            f'-DmaxErrors={max_errors}', '-DwarningAsError=false',
            '-o', str(olean), '-i', str(ilean), str(source),
        ], cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
    text = log.read_text(encoding='utf-8', errors='replace')
    matches = list(ERROR_RE.finditer(text)) if stem == 'Mock2_FunctionalAnalysis' else []
    return Metric(
        p.returncode,
        int(matches[0].group(1)) if matches else 0,
        int(matches[0].group(2)) if matches else 0,
        len(matches),
        olean.exists() and olean.stat().st_size > 0,
        ilean.exists() and ilean.stat().st_size > 0,
    )


def offsets(lines: list[str]) -> list[int]:
    result = [0]
    total = 0
    for line in lines:
        total += len(line) + 1
        result.append(total)
    return result


def declaration_region(text: str, error_line: int) -> dict[str, int | str] | None:
    lines = text.splitlines()
    if not 1 <= error_line <= len(lines):
        return None
    start_line = None
    for number in range(error_line, 0, -1):
        if DECL_START_RE.match(lines[number - 1]):
            start_line = number
            break
    if start_line is None:
        return None
    end_line = len(lines) + 1
    for number in range(start_line + 1, len(lines) + 1):
        if BOUNDARY_RE.match(lines[number - 1]):
            end_line = number
            break
    pos = offsets(lines)
    start = pos[start_line - 1]
    end = pos[end_line - 1] if end_line <= len(lines) else len(text)
    segment = text[start:end]
    proof = list(re.finditer(r':=\s*by\b', segment))
    return {
        'start_line': start_line,
        'end_line_exclusive': end_line,
        'start': start,
        'end': end,
        'segment': segment,
        'proof_match_start': proof[-1].start() if proof else -1,
        'proof_match_end': proof[-1].end() if proof else -1,
    }


def line_stable_replacement(segment: str, prefix_through_assign: str, proof: str) -> str | None:
    target_newlines = segment.count('\n')
    candidate = prefix_through_assign + ' ' + proof.rstrip() + '\n'
    current_newlines = candidate.count('\n')
    if current_newlines > target_newlines:
        return None
    candidate += '\n' * (target_newlines - current_newlines)
    if candidate.count('\n') != target_newlines:
        return None
    return candidate


def added_lines(old: str, new: str) -> list[str]:
    return [
        line[1:] for line in difflib.unified_diff(
            old.splitlines(), new.splitlines(), lineterm='')
        if line.startswith('+') and not line.startswith('+++')
    ]


def audit(old: str, new: str, old_total_lines: int) -> tuple[bool, str]:
    if old == new:
        return False, 'no change'
    if len(new.splitlines()) != old_total_lines:
        return False, 'line count changed, so frontier metric would not be comparable'
    bad = [line for line in added_lines(old, new) if PROHIBITED_RE.search(line)]
    if bad:
        return False, 'prohibited addition: ' + ' | '.join(bad[:5])
    return True, 'line-stable and proof-bypass-token clean'


def candidate_sources(current: str, metric: Metric) -> tuple[list[tuple[str, str]], dict[str, object]]:
    region = declaration_region(current, metric.first_error_line)
    diagnostic: dict[str, object] = {
        'first_error_line': metric.first_error_line,
        'first_error_col': metric.first_error_col,
        'region_found': region is not None,
    }
    candidates: list[tuple[str, str]] = []
    lines = current.splitlines(keepends=True)

    if 1 <= metric.first_error_line <= len(lines):
        idx = metric.first_error_line - 1
        original = lines[idx]
        indent = original[:len(original) - len(original.lstrip())]
        stripped = original.strip()
        local_variants: list[tuple[str, str]] = []
        if stripped == 'rfl':
            local_variants += [('local-rfl-to-simp', indent + 'simp\n'),
                               ('local-rfl-to-simpa', indent + 'simpa\n')]
        if stripped == 'simp':
            local_variants.append(('local-simp-to-simpa', indent + 'simpa\n'))
        if stripped.startswith('exact ') and stripped.count('\n') == 0:
            expr = stripped[len('exact '):]
            local_variants.append(
                ('local-exact-to-simpa-using', indent + f'simpa using ({expr})\n'))
        if stripped.startswith('apply ') and '?' not in stripped:
            expr = stripped[len('apply '):]
            local_variants.append(
                ('local-apply-to-exact', indent + f'exact {expr}\n'))
        if stripped.startswith('simpa using '):
            expr = stripped[len('simpa using '):]
            local_variants.append(
                ('local-simpa-using-to-exact', indent + f'exact {expr}\n'))
        for name, replacement in local_variants:
            changed = lines.copy()
            changed[idx] = replacement
            candidates.append((name, ''.join(changed)))

    if region is None:
        return candidates, diagnostic
    start = int(region['start'])
    end = int(region['end'])
    segment = str(region['segment'])
    proof_start = int(region['proof_match_start'])
    diagnostic.update({
        'declaration_start_line': int(region['start_line']),
        'declaration_end_line_exclusive': int(region['end_line_exclusive']),
        'proof_assignment_found': proof_start >= 0,
    })
    if proof_start < 0:
        return candidates, diagnostic

    prefix_through_assign = segment[:proof_start + 2]
    proofs = [
        ('whole-classical-aesop', 'by\n  classical\n  aesop'),
        ('whole-classical-simp-all', 'by\n  classical\n  simp_all'),
        ('whole-classical-grind', 'by\n  classical\n  grind'),
        ('whole-aesop', 'by\n  aesop'),
        ('whole-simpa', 'by\n  simpa'),
        ('whole-classical-ext-simp', 'by\n  classical\n  ext <;> simp_all'),
        ('whole-classical-constructor-aesop', 'by\n  classical\n  constructor <;> aesop'),
        ('whole-classical-aesop-query', 'by\n  classical\n  aesop?'),
        ('whole-classical-simp-query', 'by\n  classical\n  simp?'),
        ('whole-classical-exact-query', 'by\n  classical\n  exact?'),
    ]
    for name, proof in proofs:
        replacement = line_stable_replacement(segment, prefix_through_assign, proof)
        if replacement is None:
            continue
        candidates.append((name, current[:start] + replacement + current[end:]))
    return candidates, diagnostic


def compact_log(source: Path, target: Path, metric: Metric) -> None:
    text = source.read_text(encoding='utf-8', errors='replace')
    matches = list(ERROR_RE.finditer(text))
    if not matches:
        target.write_text(text[:20000], encoding='utf-8')
        return
    start = max(0, matches[0].start() - 800)
    end = min(len(text), matches[min(10, len(matches)) - 1].start() + 3500)
    target.write_text(text[start:end], encoding='utf-8')


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    baseline_bytes = SRC.read_bytes()
    baseline_sha = digest(baseline_bytes)
    if baseline_sha != EXPECTED_SHA:
        raise SystemExit(f'baseline SHA mismatch: {baseline_sha}')
    if not (ROOT / 'build-logs/fa-pass376-champion-reproduction/REPRODUCED_31725_OR_BETTER').exists():
        raise SystemExit('authoritative reproduction marker missing')

    prerequisites: dict[str, dict[str, object]] = {}
    for stem in ('Mock2', 'Mock2_Advanced'):
        m = compile_module(stem, LOGS / f'{stem}.log', 500)
        prerequisites[stem] = asdict(m)
        if not m.passed:
            raise SystemExit(f'prerequisite {stem} failed')

    baseline_metric = compile_module(
        'Mock2_FunctionalAnalysis', LOGS / 'baseline.log', 1400)
    if not baseline_metric.passed and baseline_metric.first_error_line < REQUIRED_FRONTIER:
        raise SystemExit(
            f'baseline regression: {baseline_metric.first_error_line} < {REQUIRED_FRONTIER}')

    current = baseline_bytes.decode('utf-8')
    current_metric = baseline_metric
    current_sha = baseline_sha
    compile_count = 0
    rounds = 0
    records: list[dict[str, object]] = []
    accepted: list[dict[str, object]] = []

    while not current_metric.passed and compile_count < MAX_COMPILES:
        rounds += 1
        generated, diagnostic = candidate_sources(current, current_metric)
        (OUT / f'round{rounds:02d}-diagnostic.json').write_text(
            json.dumps(diagnostic, indent=2) + '\n', encoding='utf-8')
        if not generated:
            break
        seen: set[str] = set()
        best: tuple[str, str, str, Metric] | None = None
        for index, (name, candidate) in enumerate(generated, 1):
            if compile_count >= MAX_COMPILES:
                break
            candidate_sha = hashlib.sha256(candidate.encode()).hexdigest()
            if candidate_sha in seen:
                continue
            seen.add(candidate_sha)
            ok, audit_reason = audit(current, candidate, len(current.splitlines()))
            if not ok:
                records.append({
                    'round': rounds, 'name': name, 'input_sha256': current_sha,
                    'output_sha256': candidate_sha, 'compiled': False,
                    'promoted': False, 'reason': audit_reason,
                })
                continue
            SRC.write_text(candidate, encoding='utf-8')
            compile_count += 1
            log = LOGS / f'round{rounds:02d}-{index:02d}-{name}-{candidate_sha[:10]}.log'
            metric = compile_module('Mock2_FunctionalAnalysis', log, 1400)
            compact_log(log, OUT / f'round{rounds:02d}-{index:02d}-{name}.context.txt', metric)
            strictly_better = metric.passed or (
                not current_metric.passed and
                metric.first_error_line > current_metric.first_error_line
            )
            record = {
                'round': rounds, 'name': name, 'input_sha256': current_sha,
                'output_sha256': candidate_sha, 'compiled': True,
                'metric': asdict(metric), 'promoted': False,
                'reason': (
                    'strict improvement' if strictly_better else
                    f'not better than current first error {current_metric.first_error_line}'
                ),
            }
            records.append(record)
            if strictly_better and (best is None or metric.score > best[3].score):
                best = (name, candidate, candidate_sha, metric)
            SRC.write_text(current, encoding='utf-8')

        if best is None:
            break
        name, current, current_sha, new_metric = best
        for record in reversed(records):
            if record.get('output_sha256') == current_sha:
                record['promoted'] = True
                break
        accepted.append({
            'round': rounds,
            'name': name,
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
        'rounds': rounds,
        'accepted_chain': accepted,
        'candidate_records': records,
        'prerequisites': prerequisites,
        'line_count_preserved': len(current.splitlines()) == len(
            baseline_bytes.decode('utf-8').splitlines()),
        'declaration_signatures_preserved_by_construction': True,
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
        f"candidate_compiles={compile_count}\n",
        encoding='utf-8')
    print((OUT / 'RESULT.txt').read_text())
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
