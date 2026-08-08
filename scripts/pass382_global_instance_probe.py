from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

import lean_repair_loop_v377 as guard
import priority_chain_v378 as chain

TARGET = ROOT / 'PrimalitySheafVerification' / 'Mock2_FunctionalAnalysis.lean'
OUT = Path('/tmp/pass382-global-instance')
OUT.mkdir(parents=True, exist_ok=True)


def digest(text: str) -> str:
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def insertion_index(lines: list[str]) -> int:
    for i, line in enumerate(lines):
        if re.match(r'^\s*noncomputable\s+section\s*$', line):
            return i + 1
    last_import = -1
    for i, line in enumerate(lines):
        if re.match(r'^\s*(?:public\s+)?import\s+', line):
            last_import = i
    return last_import + 1


def insert(text: str, additions: list[str]) -> str:
    lines = text.splitlines()
    idx = insertion_index(lines)
    payload = [''] + additions + ['']
    result = lines[:idx] + payload + lines[idx:]
    return '\n'.join(result) + ('\n' if text.endswith('\n') else '')


def result_metrics(result: dict[str, Any], delta: int = 0) -> dict[str, Any]:
    line = result.get('first_error_line')
    adjusted = line - max(0, delta) if isinstance(line, int) else None
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


def improves(c: dict[str, Any], b: dict[str, Any]) -> bool:
    if c['exit_code'] == 0 and c['artifacts_ok']:
        return True
    if c['error_headers'] < b['error_headers']:
        return True
    a, z = c.get('adjusted_first_error_line'), b.get('adjusted_first_error_line')
    return isinstance(a, int) and isinstance(z, int) and a > z


def score(row: dict[str, Any]) -> tuple[int, int, int]:
    m = row['metrics']
    return (
        int(m['exit_code'] == 0 and m['artifacts_ok']),
        -int(m['error_headers']),
        m['adjusted_first_error_line'] if isinstance(m.get('adjusted_first_error_line'), int) else -1,
    )


def main() -> int:
    baseline = TARGET.read_text(encoding='utf-8')
    headers = guard.declaration_headers(baseline)
    imports = guard.imports(baseline)
    if guard.forbidden_hits(baseline):
        raise SystemExit('baseline contains forbidden executable token(s)')
    baseline_result = chain.compile_one(TARGET, 'pass382-baseline', max_errors=60)
    baseline_metrics = result_metrics(baseline_result)
    if baseline_result['exit_code'] == 0 and baseline_result['artifacts_ok']:
        payload = {'already_passed': True, 'baseline': baseline_metrics}
        (OUT / 'summary.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
        (OUT / 'IMPROVED').write_text('already-pass\n', encoding='utf-8')
        return 0

    canonical_add = (
        'local instance pass382CanonicalComplexAddCommGroup : AddCommGroup ℂ :=\n'
        '  Complex.instNormedAddCommGroup.toAddCommGroup'
    )
    canonical_module = (
        'local instance pass382CanonicalComplexRealModule : Module ℝ ℂ :=\n'
        '  Complex.instNormedSpaceReal.toModule'
    )
    infer_add = (
        'local instance pass382InferredComplexAddCommGroup : AddCommGroup ℂ :=\n'
        '  (inferInstance : NormedAddCommGroup ℂ).toAddCommGroup'
    )
    infer_module = (
        'local instance pass382InferredComplexRealModule : Module ℝ ℂ :=\n'
        '  (inferInstance : NormedSpace ℝ ℂ).toModule'
    )

    candidates = {
        'file-canonical-add': insert(baseline, canonical_add.splitlines()),
        'file-canonical-module': insert(baseline, canonical_module.splitlines()),
        'file-canonical-add-module': insert(
            baseline, canonical_add.splitlines() + [''] + canonical_module.splitlines()
        ),
        'file-infer-add-module': insert(
            baseline, infer_add.splitlines() + [''] + infer_module.splitlines()
        ),
        'replace-legacy-plus-file-canonical': insert(
            baseline.replace(
                'Complex.addCommGroup',
                'Complex.instNormedAddCommGroup.toAddCommGroup',
            ),
            canonical_add.splitlines() + [''] + canonical_module.splitlines(),
        ),
        'remove-local-add-plus-file-canonical': insert(
            '\n'.join(
                line for line in baseline.splitlines()
                if not re.match(r'^\s*(?:letI|haveI)\s*:\s*AddCommGroup\s+ℂ\s*:=', line)
            ) + ('\n' if baseline.endswith('\n') else ''),
            canonical_add.splitlines() + [''] + canonical_module.splitlines(),
        ),
    }

    rows = [{'label': 'baseline', 'metrics': baseline_metrics, 'accepted': True}]
    source_map: dict[str, str] = {}
    seen = {digest(baseline)}
    baseline_lines = len(baseline.splitlines())
    for label, source in candidates.items():
        h = digest(source)
        if h in seen:
            continue
        seen.add(h)
        accepted = True
        reason = ''
        if guard.declaration_headers(source) != headers:
            accepted = False
            reason = 'public declaration header changed'
        elif not imports.issubset(guard.imports(source)):
            accepted = False
            reason = 'existing import removed'
        elif guard.forbidden_hits(source):
            accepted = False
            reason = f'forbidden token(s): {guard.forbidden_hits(source)}'
        if accepted:
            TARGET.write_text(source, encoding='utf-8')
            result = chain.compile_one(TARGET, f'candidate-{label}', max_errors=60)
            m = result_metrics(result, len(source.splitlines()) - baseline_lines)
        else:
            m = {
                'exit_code': 999,
                'artifacts_ok': False,
                'error_headers': 10**9,
                'first_error_line': None,
                'adjusted_first_error_line': None,
                'first_error_message': reason,
                'source_sha256': h,
                'log': None,
            }
        rows.append({'label': label, 'metrics': m, 'accepted': accepted, 'reason': reason})
        source_map[label] = source
        TARGET.write_text(baseline, encoding='utf-8')

    improving = [r for r in rows[1:] if r['accepted'] and improves(r['metrics'], baseline_metrics)]
    best = max(improving, key=score) if improving else rows[0]
    if best['label'] != 'baseline':
        TARGET.write_text(source_map[best['label']], encoding='utf-8')
        (OUT / 'best-candidate.lean').write_text(source_map[best['label']], encoding='utf-8')
        (OUT / 'IMPROVED').write_text(
            f"label={best['label']}\nsha256={digest(source_map[best['label']])}\n",
            encoding='utf-8',
        )
    else:
        TARGET.write_text(baseline, encoding='utf-8')
        (OUT / 'NO_IMPROVEMENT').write_text('No file-level instance candidate improved.\n', encoding='utf-8')

    payload = {
        'baseline_sha256': digest(baseline),
        'baseline': rows[0],
        'candidates': rows[1:],
        'best': best,
        'objectively_improved': best['label'] != 'baseline',
    }
    (OUT / 'summary.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
    print(json.dumps(payload, indent=2))
    return 0 if best['label'] != 'baseline' else 2


if __name__ == '__main__':
    raise SystemExit(main())
