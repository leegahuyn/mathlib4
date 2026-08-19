#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import importlib.util
import json
import os
import shutil
import subprocess
import sys

os.environ.setdefault('OUT', '/tmp/qym-generic-first-pass')
base_path = Path(os.environ.get('BASE_DRIVER', '.github/qym_v11_edgeparametertransport_driver.py'))
spec = importlib.util.spec_from_file_location('qym_generic_base', base_path)
if spec is None or spec.loader is None:
    raise SystemExit(f'cannot load base driver: {base_path}')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)

PATCHER = Path(os.environ['PATCHER'])
VARIANTS = tuple(item for item in os.environ['VARIANTS'].split(',') if item)
GATE_FIELD = os.environ.get('GATE_FIELD', 'producer_fixed')
SELECTION_SCHEMA = os.environ.get('SELECTION_SCHEMA', 'qym-generic-first-pass-selection-v1')


def main() -> int:
    if not VARIANTS:
        raise SystemExit('VARIANTS is empty')
    base.OUT.mkdir(parents=True, exist_ok=True)
    canonical = base.OUT / 'QYM.checked-in.lean'
    shutil.copy2(base.QYM, canonical)
    try:
        raw = canonical.read_bytes()
        check = {
            'source_sha256': base.sha256(raw),
            'source_blob': base.git_blob(raw),
            'expected_sha256': base.BASE_SHA256,
            'expected_blob': base.BASE_BLOB,
            'errors': base.BASE_ERRORS,
            'run_id': base.BASE_RUN_ID,
            'job_id': base.BASE_JOB_ID,
            'sha_ok': base.sha256(raw) == base.BASE_SHA256,
            'blob_ok': base.git_blob(raw) == base.BASE_BLOB,
        }
        base.write_json(base.OUT / 'BASELINE_CHECK.json', check)
        if not check['sha_ok'] or not check['blob_ok']:
            raise RuntimeError(f'baseline mismatch: {check}')

        rows: list[dict[str, object]] = []
        for variant in VARIANTS:
            candidate = base.OUT / f'QYM.candidate-{variant}.lean'
            shutil.copy2(canonical, candidate)
            patch_path = base.OUT / f'{variant}.PATCH_RESULT.json'
            with patch_path.open('wb') as handle:
                subprocess.run(
                    [sys.executable, '-B', str(PATCHER), variant,
                     str(candidate), base.BASE_SHA256],
                    check=True, stdout=handle,
                )
            patch = json.loads(patch_path.read_text(encoding='utf-8'))
            candidate_raw = candidate.read_bytes()
            if patch.get('input_sha256') != base.BASE_SHA256 or patch.get('input_blob') != base.BASE_BLOB:
                raise RuntimeError(f'{variant}: input authority mismatch')
            if patch.get('candidate_sha256') != base.sha256(candidate_raw) or patch.get('candidate_blob') != base.git_blob(candidate_raw):
                raise RuntimeError(f'{variant}: candidate digest mismatch')
            if any(int(value) != 0 for value in (patch.get('forbidden') or {}).values()):
                raise RuntimeError(f'{variant}: forbidden-token audit failed')

            local = base.compile_candidate(candidate, variant, 'local', 1)
            first = local.get('first_error') or {}
            first_line = int(first.get('line') or 10**9)
            gate_line = int(patch['gate_line'])
            gate_pass = int(local['panic_lines']) == 0 and first_line >= gate_line
            local['gate_line'] = gate_line
            local[GATE_FIELD] = gate_pass
            base.write_json(base.OUT / f'{variant}.LOCAL_RESULT.json', local)
            row: dict[str, object] = {
                'variant': variant,
                'candidate': str(candidate),
                'patch': patch,
                'local': local,
                'local_gate_pass': gate_pass,
            }
            rows.append(row)
            if not gate_pass:
                continue

            full = base.compile_candidate(candidate, variant, 'full', 10000)
            semantic_pass = (
                int(full['exit']) == 0 and int(full['error_headers']) == 0 and
                int(full['panic_lines']) == 0 and bool(full['olean_exists']) and bool(full['ilean_exists'])
            )
            strict = semantic_pass or (
                int(full['panic_lines']) == 0 and int(full['error_headers']) < base.BASE_ERRORS
            )
            full.update({
                'semantic_pass': semantic_pass,
                'strict_improvement': strict,
                'baseline_error_headers': base.BASE_ERRORS,
                'baseline_qym_sha256': base.BASE_SHA256,
                'baseline_qym_blob': base.BASE_BLOB,
                'candidate_qym_sha256': patch['candidate_sha256'],
                'candidate_qym_blob': patch['candidate_blob'],
                'run_id': os.environ.get('GITHUB_RUN_ID'),
                'trigger_sha': os.environ.get('GITHUB_SHA'),
            })
            row['full'] = full
            base.write_json(base.OUT / f'{variant}.FULL_RESULT.json', full)
            if strict:
                shutil.copy2(candidate, base.OUT / 'QYM.best.lean')
                base.write_json(base.OUT / 'BEST_RESULT.json', full)
                selection = {
                    'schema': SELECTION_SCHEMA,
                    'baseline': check,
                    'candidates': rows,
                    'best_variant': variant,
                    'best': full,
                    'strict_improvement_found': True,
                }
                base.write_json(base.OUT / 'SELECTION.json', selection)
                print(json.dumps(selection, indent=2, sort_keys=True))
                return 0

        selection = {
            'schema': SELECTION_SCHEMA,
            'baseline': check,
            'candidates': rows,
            'strict_improvement_found': False,
        }
        base.write_json(base.OUT / 'SELECTION.json', selection)
        print(json.dumps(selection, indent=2, sort_keys=True))
        return 2
    except Exception as exc:
        (base.OUT / 'FATAL.txt').write_text(f'{type(exc).__name__}: {exc}\n', encoding='utf-8')
        raise
    finally:
        if canonical.exists():
            shutil.copy2(canonical, base.QYM)


if __name__ == '__main__':
    raise SystemExit(main())
