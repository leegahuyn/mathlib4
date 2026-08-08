from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

import lean_repair_loop_v377 as guard
import priority_chain_v378 as chain
import run_lean_repair_v380_styled as model_backend

OUT = Path('/tmp/pass384-declaration-agent')
OUT.mkdir(parents=True, exist_ok=True)
PUBLIC_COMMAND = re.compile(
    r'^(?:(?:@\[[^\n]*\]\s*)?)(?:(?:noncomputable|protected|private|local)\s+)*'
    r'(?:theorem|lemma|corollary|def|abbrev|structure|class|instance)\b'
)
BOUNDARY = re.compile(
    r'^(?:end\b|namespace\b|section\b|open\b|variable\b|include\b|omit\b|'
    r'attribute\b|local\s+notation\b|notation\b|scoped\b|set_option\b|#|'
    r'noncomputable\s+section\b)'
)
STYLES = [
    ('gpt5-exact', 'openai/gpt-5,openai/gpt-4.1,openai/gpt-4o',
     'Repair the exact declaration by resolving the first expected/actual type mismatch at its root.'),
    ('gpt41-api', 'openai/gpt-4.1,openai/gpt-5,openai/gpt-4o',
     'Use current mathlib APIs, explicit coercions, typed intermediate facts, and dependent transports.'),
    ('gpt4o-proof', 'openai/gpt-4o,openai/gpt-4.1,openai/gpt-5',
     'Rewrite the proof conservatively with calc, change, ext, rw, and simpa only.'),
]


def sha(text: str) -> str:
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ['git', *args], cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=check
    )


def declaration_span(lines: list[str], line_no: int) -> tuple[int, int]:
    idx = max(0, min(len(lines) - 1, line_no - 1))
    start = None
    attr_start = None
    for i in range(idx, -1, -1):
        line = lines[i]
        if PUBLIC_COMMAND.match(line):
            start = attr_start if attr_start is not None and attr_start < i else i
            break
        if line.startswith('@['):
            attr_start = i
        elif line and not line[0].isspace() and not line.startswith('/-') and not line.startswith('--'):
            attr_start = None
    if start is None:
        raise RuntimeError(f'could not locate a declaration before line {line_no}')
    end = len(lines)
    in_block_comment = False
    for i in range(start + 1, len(lines)):
        line = lines[i]
        stripped = line.strip()
        if '/*' in line or '/-' in line:
            in_block_comment = True
        if in_block_comment:
            if '-/' in line:
                in_block_comment = False
            continue
        if not line:
            continue
        if line[0].isspace():
            continue
        if PUBLIC_COMMAND.match(line) or BOUNDARY.match(line) or line.startswith('@[') or line.startswith('/-!') or line.startswith('/--'):
            end = i
            break
    return start, end


def compiler_excerpt(output: str, max_errors: int = 8) -> str:
    lines = output.splitlines()
    indexes = [i for i, line in enumerate(lines) if re.search(r'\.lean:\d+:\d+: error:', line)]
    kept: list[str] = []
    for idx in indexes[:max_errors]:
        lo = max(0, idx)
        hi = min(len(lines), idx + 18)
        kept.extend(lines[lo:hi])
        kept.append('')
    return '\n'.join(kept)[:32000]


def extract_block(response: str) -> str:
    marker = re.search(r'<<<LEAN>>>\s*(.*?)\s*<<<END>>>', response, flags=re.S)
    if marker:
        return marker.group(1).strip() + '\n'
    fenced = re.findall(r'```(?:lean|lean4)?\s*\n(.*?)```', response, flags=re.S)
    for block in fenced:
        if re.search(r'\b(?:theorem|lemma|corollary|def|abbrev|structure|class|instance)\b', block):
            return block.strip() + '\n'
    raise RuntimeError('model returned no complete Lean declaration block')


def objective(new: dict[str, Any], old: dict[str, Any], delta: int) -> bool:
    if new['exit_code'] == 0 and new['artifacts_ok']:
        return True
    if new['error_headers'] < old['error_headers']:
        return True
    a = new.get('first_error_line')
    b = old.get('first_error_line')
    if isinstance(a, int) and isinstance(b, int) and a - max(delta, 0) > b:
        return True
    return False


def commit_progress(target: Path, payload: dict[str, Any], iteration: int) -> None:
    branch = os.environ.get('AUTO_PUSH_BRANCH', '').strip()
    if not branch:
        return
    status = ROOT / 'build-logs' / 'PASS384_DECLARATION_CURRENT.json'
    archive = ROOT / 'build-logs' / f'PASS384_DECLARATION_ITER_{iteration:03d}.json'
    status.parent.mkdir(exist_ok=True)
    text = json.dumps(payload, indent=2, ensure_ascii=False)
    status.write_text(text, encoding='utf-8')
    archive.write_text(text, encoding='utf-8')
    git('config', 'user.name', 'github-actions[bot]')
    git('config', 'user.email', '41898282+github-actions[bot]@users.noreply.github.com')
    git('add', str(target.relative_to(ROOT)), str(status.relative_to(ROOT)), str(archive.relative_to(ROOT)))
    if git('diff', '--cached', '--quiet', check=False).returncode == 0:
        return
    git('commit', '-m', f'fix: advance declaration-level FA repair iteration {iteration}')
    push = git('push', 'origin', f'HEAD:{branch}', check=False)
    if push.returncode != 0:
        raise RuntimeError('failed to push accepted declaration repair:\n' + push.stdout)


def prompt(
    target: Path,
    source: str,
    start: int,
    end: int,
    result: dict[str, Any],
    style: str,
    iteration: int,
    rejection: str,
) -> str:
    lines = source.splitlines()
    before = '\n'.join(f'{i + 1}: {lines[i]}' for i in range(max(0, start - 80), start))
    declaration = '\n'.join(lines[start:end])
    output = Path(result['log']).read_text(encoding='utf-8', errors='replace')
    return f"""You are repairing `{target.relative_to(ROOT)}` for Lean 4.33.0-rc1 and the pinned mathlib checkout.

Return exactly one complete replacement for the failing declaration, enclosed by:
<<<LEAN>>>
...complete declaration...
<<<END>>>

Hard constraints:
- Preserve the existing declaration attributes, name, binders, assumptions, result type, and visibility exactly.
- Change only its implementation/proof body. Do not add assumptions or weaken the conclusion.
- Do not use sorry, admit, a new axiom, unsafe, native_decide, or Lean.ofReduceBool.
- Do not introduce a public helper. A local have/let inside the proof is allowed.
- Use current mathlib APIs and kernel-checkable proof terms.
- {style}

Iteration: {iteration}
Current compiler result: exit={result['exit_code']}, errors={result['error_headers']}, first={result['first_error_line']}
{('Previous rejection: ' + rejection) if rejection else ''}

Compiler errors:
```text
{compiler_excerpt(output)}
```

Nearby definitions before the declaration:
```lean
{before[-24000:]}
```

Complete declaration to replace:
```lean
{declaration}
```
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--target', required=True)
    parser.add_argument('--iterations', type=int, default=20)
    parser.add_argument('--deadline-seconds', type=int, default=18000)
    args = parser.parse_args()
    target = (ROOT / args.target).resolve()
    deadline = time.monotonic() + args.deadline_seconds
    source = target.read_text(encoding='utf-8')
    baseline_headers = guard.declaration_headers(source)
    baseline_imports = guard.imports(source)
    if guard.forbidden_hits(source):
        raise SystemExit('baseline source contains forbidden executable token(s)')

    current = chain.compile_one(target, 'declaration-initial', max_errors=100)
    history: list[dict[str, Any]] = [dict(current)]
    progress = False
    for iteration in range(1, args.iterations + 1):
        if current['exit_code'] == 0 and current['artifacts_ok']:
            break
        if time.monotonic() >= deadline:
            break
        line = current.get('first_error_line')
        if not isinstance(line, int):
            break
        source = target.read_text(encoding='utf-8')
        lines = source.splitlines()
        start, end = declaration_span(lines, line)
        original_block = '\n'.join(lines[start:end]) + ('\n' if end > start else '')
        rejection = ''
        accepted = False
        for attempt_index, (slug, models, style) in enumerate(STYLES, 1):
            if time.monotonic() >= deadline:
                break
            os.environ['MODEL_CANDIDATES'] = models
            os.environ['REPAIR_STYLE'] = style
            request = prompt(target, source, start, end, current, style, iteration, rejection)
            (OUT / f'iteration-{iteration:03d}-{slug}.prompt.txt').write_text(request, encoding='utf-8')
            try:
                model, response = model_backend.cli_model_request(request, attempt_index)
                (OUT / f'iteration-{iteration:03d}-{slug}.response.txt').write_text(response, encoding='utf-8')
                block = extract_block(response)
                candidate_lines = lines[:start] + block.rstrip('\n').splitlines() + lines[end:]
                candidate = '\n'.join(candidate_lines) + ('\n' if source.endswith('\n') else '')
                if guard.declaration_headers(candidate) != baseline_headers:
                    raise RuntimeError('public declaration header fingerprint changed')
                if not baseline_imports.issubset(guard.imports(candidate)):
                    raise RuntimeError('existing import removed')
                hits = guard.forbidden_hits(candidate)
                if hits:
                    raise RuntimeError(f'forbidden executable token(s): {hits}')
                target.write_text(candidate, encoding='utf-8')
                result = chain.compile_one(target, f'declaration-{iteration}-{slug}', max_errors=100)
                delta = len(candidate.splitlines()) - len(source.splitlines())
                record = {
                    'iteration': iteration,
                    'strategy': slug,
                    'model': model,
                    'declaration_start': start + 1,
                    'declaration_end': end,
                    'source_before_sha256': sha(source),
                    'source_after_sha256': sha(candidate),
                    'result': result,
                }
                if objective(result, current, delta):
                    history.append(record)
                    current = result
                    progress = True
                    accepted = True
                    payload = {
                        'status': 'objective-progress',
                        'target': str(target.relative_to(ROOT)),
                        'current': current,
                        'history': history,
                        'last_accept': record,
                    }
                    (OUT / 'status.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
                    commit_progress(target, payload, iteration)
                    break
                target.write_text(source, encoding='utf-8')
                rejection = (
                    f"candidate did not improve: exit={result['exit_code']}, "
                    f"errors={result['error_headers']}, first={result['first_error_line']}"
                )
                (OUT / f'iteration-{iteration:03d}-{slug}.rejected.txt').write_text(rejection + '\n', encoding='utf-8')
            except Exception as exc:
                target.write_text(source, encoding='utf-8')
                rejection = str(exc)
                (OUT / f'iteration-{iteration:03d}-{slug}.rejected.txt').write_text(rejection + '\n', encoding='utf-8')
        if not accepted:
            break

    final = {
        'target': str(target.relative_to(ROOT)),
        'pass': current['exit_code'] == 0 and current['artifacts_ok'],
        'progress': progress,
        'current': current,
        'history': history,
        'final_source_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
    }
    (OUT / 'status.json').write_text(json.dumps(final, indent=2), encoding='utf-8')
    print(json.dumps(final, indent=2))
    if final['pass']:
        return 0
    return 2 if progress else 3


if __name__ == '__main__':
    raise SystemExit(main())
