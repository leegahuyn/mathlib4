#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import collections, hashlib, json, os, re, shutil, subprocess, sys

QYM = Path('PrimalitySheafVerification/QYM.lean')
PATCHER = Path('.github/qym_patch_gb78_v13_groupoid.py')
OUT = Path('/tmp/qym-gb78-v13-groupoid-exact')
BASE_SHA = 'c1498d669d3f43cda50edf7b61b33c865b00f6fe65ea95d9f1ab3c07794d1235'
BASE_BLOB = '75c2eab05b4298d94246a6b0757f98a6ff5c02fe'
BASE_ERRORS = 78
VARIANTS = (
    'groupoid_instances',
    'groupoid_instances_fact',
    'explicit_contdiff_intermediate',
    'explicit_upper_intermediate',
    'all_instances_contdiff',
    'all_instances_upper',
)
DIAG = re.compile(r'^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$', re.M)
PANIC = re.compile(r'(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$')


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n', encoding='utf-8')


def compile_candidate(candidate: Path, variant: str, phase: str, max_errors: int):
    shutil.copy2(candidate, QYM)
    log = OUT / f'{variant}.{phase}.log'
    olean = OUT / f'{variant}.{phase}.olean'
    ilean = OUT / f'{variant}.{phase}.ilean'
    cmd = ['lake', 'env', 'lean', f'-DmaxErrors={max_errors}', '-DwarningAsError=false',
           '-o', str(olean), '-i', str(ilean), str(QYM)]
    with log.open('wb') as handle:
        proc = subprocess.run(cmd, stdout=handle, stderr=subprocess.STDOUT)
    text = log.read_text(errors='replace')
    diagnostics = []
    for match in DIAG.finditer(text):
        row = match.groupdict()
        row['line'] = int(row['line'])
        row['column'] = int(row['column'])
        diagnostics.append(row)
    errors = [row for row in diagnostics if row['severity'] == 'error']
    warnings = [row for row in diagnostics if row['severity'] == 'warning']
    result = {
        'variant': variant,
        'phase': phase,
        'exit': proc.returncode,
        'error_headers': len(errors),
        'warning_headers': len(warnings),
        'panic_lines': len(PANIC.findall(text)),
        'first_error': errors[0] if errors else None,
        'last_error': errors[-1] if errors else None,
        'errors': errors,
        'error_codes': dict(sorted(collections.Counter((row.get('code') or 'uncoded') for row in errors).items())),
        'log_sha256': sha(log.read_bytes()),
        'candidate_qym_sha256': sha(candidate.read_bytes()),
        'candidate_qym_blob': blob(candidate.read_bytes()),
        'olean_exists': olean.is_file() and olean.stat().st_size > 0,
        'ilean_exists': ilean.is_file() and ilean.stat().st_size > 0,
    }
    dump(OUT / f'{variant}.{phase}.json', result)
    return result


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    original = OUT / 'QYM.GB78.lean'
    shutil.copy2(QYM, original)
    raw = original.read_bytes()
    baseline = {
        'sha256': sha(raw), 'blob': blob(raw), 'errors': BASE_ERRORS,
        'sha_ok': sha(raw) == BASE_SHA, 'blob_ok': blob(raw) == BASE_BLOB,
        'run_id': '32267726196', 'job_id': '96115476882',
    }
    dump(OUT / 'BASELINE_CHECK.json', baseline)
    if not baseline['sha_ok'] or not baseline['blob_ok']:
        raise SystemExit(f'GB78 authority mismatch: {baseline}')

    rows = []
    try:
        for variant in VARIANTS:
            candidate = OUT / f'QYM.candidate-{variant}.lean'
            shutil.copy2(original, candidate)
            patch_path = OUT / f'{variant}.PATCH_RESULT.json'
            with patch_path.open('wb') as handle:
                subprocess.run([sys.executable, '-B', str(PATCHER), variant,
                                str(candidate), BASE_SHA], check=True, stdout=handle)
            patch = json.loads(patch_path.read_text(encoding='utf-8'))
            local = compile_candidate(candidate, variant, 'local', 12)
            lo = int(patch['section_start_line'])
            hi = int(patch['section_end_line']) + 3
            section_errors = [e for e in local.get('errors', []) if lo <= int(e['line']) <= hi]
            local_pass = int(local['panic_lines']) == 0 and not section_errors
            row = {
                'variant': variant,
                'candidate': str(candidate),
                'patch': patch,
                'local': local,
                'section_errors': section_errors,
                'local_gate_pass': local_pass,
            }
            rows.append(row)
            if not local_pass:
                continue

            full = compile_candidate(candidate, variant, 'full', 10000)
            semantic = (int(full['exit']) == 0 and int(full['error_headers']) == 0 and
                        int(full['panic_lines']) == 0 and bool(full['olean_exists']) and bool(full['ilean_exists']))
            strict = semantic or (int(full['panic_lines']) == 0 and int(full['error_headers']) < BASE_ERRORS)
            full.update({
                'semantic_pass': semantic,
                'strict_improvement': strict,
                'baseline_error_headers': BASE_ERRORS,
                'baseline_qym_sha256': BASE_SHA,
                'baseline_qym_blob': BASE_BLOB,
                'run_id': os.environ.get('GITHUB_RUN_ID'),
                'trigger_sha': os.environ.get('GITHUB_SHA'),
            })
            dump(OUT / f'{variant}.FULL_RESULT.json', full)
            row['full'] = full
            if strict:
                shutil.copy2(candidate, OUT / 'QYM.best.lean')
                dump(OUT / 'BEST_RESULT.json', full)
                dump(OUT / 'SELECTION.json', {
                    'schema': 'qym-gb78-v13-groupoid-selection-v1',
                    'baseline': baseline,
                    'candidates': rows,
                    'strict_improvement_found': True,
                    'best_variant': variant,
                    'best': full,
                })
                return 0

        dump(OUT / 'SELECTION.json', {
            'schema': 'qym-gb78-v13-groupoid-selection-v1',
            'baseline': baseline,
            'candidates': rows,
            'strict_improvement_found': False,
        })
        return 2
    finally:
        shutil.copy2(original, QYM)

if __name__ == '__main__':
    raise SystemExit(main())
