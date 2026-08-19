#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import importlib.util
import json
import os
import shutil
import subprocess
import sys

os.environ.setdefault('OUT', '/tmp/qym-v11-edgeparametertransport-fast')
base_path = Path('.github/qym_v11_edgeparametertransport_driver.py')
spec = importlib.util.spec_from_file_location('qym_v11_base', base_path)
if spec is None or spec.loader is None:
    raise SystemExit('cannot load V11 base driver')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
base.VARIANTS = ('letI_change', 'letI_simpa', 'transparent_simpa')


def main() -> int:
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
            raise RuntimeError(f'V11 baseline mismatch: {check}')

        rows: list[dict[str, object]] = []
        for variant in base.VARIANTS:
            candidate = base.OUT / f'QYM.candidate-{variant}.lean'
            shutil.copy2(canonical, candidate)
            patch_path = base.OUT / f'{variant}.PATCH_RESULT.json'
            with patch_path.open('wb') as handle:
                subprocess.run(
                    [sys.executable, '-B', str(base.PATCHER), variant,
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
            local['edgeParameterTransport_fixed'] = gate_pass
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
                    'schema': 'qym-v11-edgeparametertransport-fast-selection-v1',
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
            'schema': 'qym-v11-edgeparametertransport-fast-selection-v1',
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
