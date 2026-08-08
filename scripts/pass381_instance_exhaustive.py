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
OUT = Path('/tmp/pass381-instance-exhaustive')
OUT.mkdir(parents=True, exist_ok=True)

DECL = re.compile(
    r'^\s*(?:(?:noncomputable|protected|private|local)\s+)*'
    r'(?:theorem|lemma|corollary|def|abbrev|structure|class)\s+'
)


def digest(text: str) -> str:
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def declaration_bounds(lines: list[str], error_line: int) -> tuple[int, int, int]:
    idx = max(0, min(len(lines) - 1, error_line - 1))
    start = 0
    for i in range(idx, -1, -1):
        if DECL.match(lines[i]):
            start = i
            break
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if DECL.match(lines[i]):
            end = i
            break
    proof = start
    for i in range(start, min(end, idx + 1)):
        if ':= by' in lines[i] or re.match(r'^\s*by\s*$', lines[i]):
            proof = i
            break
    return start, end, proof


def replace_in_range(text: str, start: int, end: int, old: str, new: str) -> str:
    lines = text.splitlines()
    block = '\n'.join(lines[start:end])
    if old not in block:
        return text
    block = block.replace(old, new)
    rebuilt = lines[:start] + block.splitlines() + lines[end:]
    return '\n'.join(rebuilt) + ('\n' if text.endswith('\n') else '')


def remove_matching_lines(text: str, start: int, end: int, pattern: re.Pattern[str]) -> str:
    lines = text.splitlines()
    rebuilt = [
        line for i, line in enumerate(lines)
        if not (start <= i < end and pattern.search(line))
    ]
    return '\n'.join(rebuilt) + ('\n' if text.endswith('\n') else '')


def insert_after_proof(text: str, proof: int, additions: list[str]) -> str:
    lines = text.splitlines()
    indent = '  '
    for i in range(proof + 1, min(len(lines), proof + 20)):
        if lines[i].strip():
            indent = re.match(r'^\s*', lines[i]).group(0)
            break
    payload = [indent + line for line in additions]
    rebuilt = lines[: proof + 1] + payload + lines[proof + 1 :]
    return '\n'.join(rebuilt) + ('\n' if text.endswith('\n') else '')


def metrics(result: dict[str, Any], line_delta: int = 0) -> dict[str, Any]:
    adjusted = result.get('first_error_line')
    if isinstance(adjusted, int):
        adjusted -= max(0, line_delta)
    return {
        'exit_code': result['exit_code'],
        'artifacts_ok': result['artifacts_ok'],
        'error_headers': result['error_headers'],
        'first_error_line': result.get('first_error_line'),
        'adjusted_first_error_line': adjusted,
        'first_error_message': result.get('first_error_message', ''),
        'source_sha256': result.get('source_sha256'),
        'log': result.get('log'),
    }


def improves(candidate: dict[str, Any], baseline: dict[str, Any]) -> bool:
    if candidate['exit_code'] == 0 and candidate['artifacts_ok']:
        return True
    if candidate['error_headers'] < baseline['error_headers']:
        return True
    a = candidate.get('adjusted_first_error_line')
    b = baseline.get('adjusted_first_error_line')
    if isinstance(a, int) and isinstance(b, int) and a > b:
        return True
    return False


def score(row: dict[str, Any]) -> tuple[int, int, int]:
    m = row['metrics']
    passed = int(m['exit_code'] == 0 and m['artifacts_ok'])
    errors = -int(m['error_headers'])
    line = m.get('adjusted_first_error_line')
    return passed, errors, line if isinstance(line, int) else -1


def main() -> int:
    baseline_source = TARGET.read_text(encoding='utf-8')
    baseline_headers = guard.declaration_headers(baseline_source)
    baseline_imports = guard.imports(baseline_source)
    if guard.forbidden_hits(baseline_source):
        raise SystemExit('baseline source contains a forbidden executable token')

    baseline_result = chain.compile_one(TARGET, 'pass381-baseline', max_errors=25)
    baseline_metrics = metrics(baseline_result)
    if baseline_result['exit_code'] == 0 and baseline_result['artifacts_ok']:
        payload = {'pass': True, 'baseline': baseline_metrics, 'already_passed': True}
        (OUT / 'summary.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
        (OUT / 'IMPROVED').write_text('already-pass\n', encoding='utf-8')
        return 0
    error_line = baseline_result.get('first_error_line')
    if not isinstance(error_line, int):
        raise SystemExit('could not parse the first Lean error line')

    lines = baseline_source.splitlines()
    start, end, proof = declaration_bounds(lines, error_line)
    context = '\n'.join(f'{i + 1}: {lines[i]}' for i in range(max(0, start - 10), min(len(lines), end + 10)))
    (OUT / 'failing-declaration-context.txt').write_text(context, encoding='utf-8')

    candidates: dict[str, str] = {}
    canonical_add = 'Complex.instNormedAddCommGroup.toAddCommGroup'
    legacy_add = 'Complex.addCommGroup'
    canonical_module = 'Complex.instNormedSpaceReal.toModule'
    infer_add = '(inferInstance : NormedAddCommGroup ℂ).toAddCommGroup'
    infer_module = '(inferInstance : NormedSpace ℝ ℂ).toModule'

    candidates['decl-replace-legacy-add-canonical'] = replace_in_range(
        baseline_source, start, end, legacy_add, canonical_add
    )
    candidates['decl-replace-canonical-add-legacy'] = replace_in_range(
        baseline_source, start, end, canonical_add, legacy_add
    )
    candidates['decl-replace-legacy-add-infer'] = replace_in_range(
        baseline_source, start, end, legacy_add, infer_add
    )
    candidates['decl-replace-canonical-add-infer'] = replace_in_range(
        baseline_source, start, end, canonical_add, infer_add
    )

    local_add_line = re.compile(r'^\s*(?:letI|haveI)\s*:\s*AddCommGroup\s+ℂ\s*:=')
    local_module_line = re.compile(r'^\s*(?:letI|haveI)\s*:\s*Module\s+ℝ\s+ℂ\s*:=')
    candidates['decl-remove-local-add'] = remove_matching_lines(
        baseline_source, start, end, local_add_line
    )
    candidates['decl-remove-local-module'] = remove_matching_lines(
        baseline_source, start, end, local_module_line
    )
    candidates['decl-remove-local-add-module'] = remove_matching_lines(
        remove_matching_lines(baseline_source, start, end, local_add_line),
        start,
        end,
        local_module_line,
    )

    insertion_sets = {
        'canonical-add': [f'letI : AddCommGroup ℂ := {canonical_add}'],
        'legacy-add': [f'letI : AddCommGroup ℂ := {legacy_add}'],
        'infer-add': [f'letI : AddCommGroup ℂ := {infer_add}'],
        'canonical-module': [f'letI : Module ℝ ℂ := {canonical_module}'],
        'infer-module': [f'letI : Module ℝ ℂ := {infer_module}'],
        'canonical-add-module': [
            f'letI : AddCommGroup ℂ := {canonical_add}',
            f'letI : Module ℝ ℂ := {canonical_module}',
        ],
        'legacy-add-canonical-module': [
            f'letI : AddCommGroup ℂ := {legacy_add}',
            f'letI : Module ℝ ℂ := {canonical_module}',
        ],
        'infer-add-module': [
            f'letI : AddCommGroup ℂ := {infer_add}',
            f'letI : Module ℝ ℂ := {infer_module}',
        ],
    }
    for label, additions in insertion_sets.items():
        candidates[f'proof-insert-{label}'] = insert_after_proof(
            baseline_source, proof, additions
        )

    stripped = candidates['decl-remove-local-add-module']
    stripped_lines = stripped.splitlines()
    stripped_error = error_line - (len(lines) - len(stripped_lines))
    s_start, s_end, s_proof = declaration_bounds(stripped_lines, stripped_error)
    for label, additions in insertion_sets.items():
        candidates[f'reset-insert-{label}'] = insert_after_proof(stripped, s_proof, additions)

    unique: dict[str, tuple[str, int]] = {}
    for label, source in candidates.items():
        if source == baseline_source:
            continue
        h = digest(source)
        if h in unique:
            continue
        unique[h] = (label, len(source.splitlines()) - len(lines))

    rows: list[dict[str, Any]] = [
        {'label': 'baseline', 'metrics': baseline_metrics, 'accepted': True, 'line_delta': 0}
    ]
    sources_by_label: dict[str, str] = {}
    for h, (label, delta) in unique.items():
        source = next(s for s in candidates.values() if digest(s) == h)
        accepted = True
        reason = ''
        if guard.declaration_headers(source) != baseline_headers:
            accepted = False
            reason = 'public declaration header fingerprint changed'
        elif not baseline_imports.issubset(guard.imports(source)):
            accepted = False
            reason = 'existing import removed'
        elif guard.forbidden_hits(source):
            accepted = False
            reason = f'forbidden token(s): {guard.forbidden_hits(source)}'
        if accepted:
            TARGET.write_text(source, encoding='utf-8')
            result = chain.compile_one(TARGET, f'candidate-{label}', max_errors=25)
            row_metrics = metrics(result, delta)
        else:
            row_metrics = {
                'exit_code': 999,
                'artifacts_ok': False,
                'error_headers': 10**9,
                'first_error_line': None,
                'adjusted_first_error_line': None,
                'first_error_message': reason,
                'source_sha256': h,
                'log': None,
            }
        rows.append({
            'label': label,
            'metrics': row_metrics,
            'accepted': accepted,
            'reason': reason,
            'line_delta': delta,
        })
        sources_by_label[label] = source
        TARGET.write_text(baseline_source, encoding='utf-8')

    baseline_row = rows[0]
    improving = [row for row in rows[1:] if row['accepted'] and improves(row['metrics'], baseline_row['metrics'])]
    best = max(improving, key=score) if improving else baseline_row
    if best['label'] != 'baseline':
        TARGET.write_text(sources_by_label[best['label']], encoding='utf-8')
        (OUT / 'IMPROVED').write_text(
            f"label={best['label']}\nsource_sha256={digest(sources_by_label[best['label']])}\n",
            encoding='utf-8',
        )
        (OUT / 'best-candidate.lean').write_text(
            sources_by_label[best['label']], encoding='utf-8'
        )
    else:
        TARGET.write_text(baseline_source, encoding='utf-8')
        (OUT / 'NO_IMPROVEMENT').write_text(
            'No tested instance normalization objectively advanced the compiler frontier.\n',
            encoding='utf-8',
        )

    payload = {
        'baseline_source_sha256': digest(baseline_source),
        'error_line': error_line,
        'declaration_start_line': start + 1,
        'declaration_end_line': end,
        'proof_start_line': proof + 1,
        'baseline': baseline_row,
        'candidates': rows[1:],
        'best': best,
        'objectively_improved': best['label'] != 'baseline',
    }
    (OUT / 'summary.json').write_text(json.dumps(payload, indent=2), encoding='utf-8')
    print(json.dumps(payload, indent=2))
    return 0 if best['label'] != 'baseline' else 2


if __name__ == '__main__':
    raise SystemExit(main())
