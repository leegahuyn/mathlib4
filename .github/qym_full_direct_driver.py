#!/usr/bin/env python3
from __future__ import annotations

import bisect
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

PATTERNS = {
    'sorry': r'\bsorry\b',
    'admit': r'\badmit\b',
    'unsafe': r'\bunsafe\b',
    'native_decide': r'\bnative_decide\b',
    'Lean.ofReduceBool': r'\bLean\.ofReduceBool\b',
    'axiom_declaration': r'(?m)^\s*(?:public\s+|private\s+)?axiom\b',
    'maxHeartbeats_zero': r'\bmaxHeartbeats\s*(?::=|=)\s*0\b',
}

def code_only(text: str) -> tuple[str, int]:
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    line = False
    while i < len(text):
        if line:
            if text[i] == '\n':
                line = False
                out.append('\n')
            else:
                out.append(' ')
            i += 1
            continue
        if depth:
            if text.startswith('/-', i):
                depth += 1
                out.extend('  ')
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
            continue
        if string:
            if text[i] == '\\' and i + 1 < len(text):
                out.extend('  ')
                i += 2
            elif text[i] == '"':
                string = False
                out.append(' ')
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
            continue
        if text.startswith('--', i):
            line = True
            out.extend('  ')
            i += 2
        elif text.startswith('/-', i):
            depth = 1
            out.extend('  ')
            i += 2
        elif text[i] == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out), depth

def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit('usage: qym_full_direct_driver.py CANDIDATE QYM_PATH OUT_DIR')
    candidate = Path(sys.argv[1])
    qym = Path(sys.argv[2])
    out = Path(sys.argv[3])
    out.mkdir(parents=True, exist_ok=True)
    text = candidate.read_text()
    code, depth = code_only(text)
    counts = {name: len(re.findall(pat, code)) for name, pat in PATTERNS.items()}
    forbidden_zero = depth == 0 and all(v == 0 for v in counts.values())
    audit = {'forbidden_zero': forbidden_zero, 'comment_depth': depth, 'counts': counts}
    (out / 'FORBIDDEN_AUDIT.json').write_text(json.dumps(audit, indent=2) + '\n')
    if not forbidden_zero:
        raise SystemExit(json.dumps(audit, indent=2))
    shutil.copy2(candidate, qym)
    log = out / 'full.log'
    olean = out / 'QYM.olean'
    ilean = out / 'QYM.ilean'
    for p in (olean, ilean):
        p.unlink(missing_ok=True)
    start = time.time()
    with log.open('wb') as f:
        proc = subprocess.run([
            'lake', 'env', 'lean', '-DmaxErrors=10000', '-DwarningAsError=false',
            '-o', str(olean), '-i', str(ilean), str(qym)
        ], stdout=f, stderr=subprocess.STDOUT)
    elapsed = int(time.time() - start)
    log_text = log.read_text(errors='replace')
    lines = text.splitlines()
    decl_re = re.compile(r'^\s*(?:(?:noncomputable|private|protected|public)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+([^\s({:\[]+)')
    decl_lines: list[int] = []
    decl_names: list[str] = []
    for no, line in enumerate(lines, 1):
        m = decl_re.match(line)
        if m:
            decl_lines.append(no)
            decl_names.append(m.group(1))
    header = re.compile(r'^(.*\.lean):(\d+):(\d+): error(?:\(([^)]+)\))?:\s*(.*)$')
    errors = []
    for line in log_text.splitlines():
        m = header.match(line)
        if not m:
            continue
        ln = int(m.group(2))
        k = bisect.bisect_right(decl_lines, ln) - 1
        errors.append({
            'file': m.group(1), 'line': ln, 'column': int(m.group(3)),
            'code': m.group(4), 'message': m.group(5),
            'enclosing_declaration': decl_names[k] if k >= 0 else None,
        })
    warnings = sum(bool(re.match(r'^.*\.lean:\d+:\d+: warning', line)) for line in log_text.splitlines())
    panic = sum(bool(re.search(r'internal error|uncaught exception|panic(!|:| )', line, re.I)) for line in log_text.splitlines())
    codes = collections.Counter((e['code'] or 'uncoded') for e in errors)
    decls = collections.Counter((e['enclosing_declaration'] or '<none>') for e in errors)
    result = {
        'schema': os.environ.get('QYM_RESULT_SCHEMA', 'qym-full-direct-v1'),
        'authority': 'actual full-QYM direct Lean',
        'run_id': int(os.environ.get('GITHUB_RUN_ID', '0')),
        'trigger_sha': os.environ.get('GITHUB_SHA'),
        'branch': os.environ.get('GITHUB_REF_NAME'),
        'exit': proc.returncode,
        'error_headers': len(errors),
        'warning_headers': warnings,
        'panic_lines': panic,
        'elapsed_seconds': elapsed,
        'first_error': errors[0] if errors else None,
        'source_sha256': hashlib.sha256(candidate.read_bytes()).hexdigest(),
        'source_blob': subprocess.check_output(['git', 'hash-object', str(candidate)], text=True).strip(),
        'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(),
        'forbidden_zero': forbidden_zero,
        'forbidden_counts': counts,
        'comment_depth': depth,
        'olean_exists': olean.is_file() and olean.stat().st_size > 0,
        'ilean_exists': ilean.is_file() and ilean.stat().st_size > 0,
        'error_codes': dict(codes),
        'error_declarations': dict(decls),
        'errors': errors,
    }
    result['pass'] = (
        result['exit'] == 0 and result['error_headers'] == 0 and result['panic_lines'] == 0
        and result['forbidden_zero'] and result['olean_exists'] and result['ilean_exists']
    )
    (out / 'FULL_RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    (out / 'RESULT.json').write_text(json.dumps({k: v for k, v in result.items() if k != 'errors'}, indent=2) + '\n')
    error_lines = []
    for e in errors:
        code_suffix = f"({e['code']})" if e['code'] else ''
        error_lines.append(
            f"{e['file']}:{e['line']}:{e['column']}: error{code_suffix}: "
            f"{e['message']} [{e['enclosing_declaration']}]"
        )
    (out / 'errors.txt').write_text('\n'.join(error_lines) + ('\n' if error_lines else ''))
    print(json.dumps({k: v for k, v in result.items() if k not in {'errors', 'forbidden_counts', 'error_declarations'}}, indent=2))

if __name__ == '__main__':
    main()
