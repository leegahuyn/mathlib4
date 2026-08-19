#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
import sys

RAW_VARIABLE = 'variable (hSmooth : SmoothTransitionResidual)'
RAW_USE = 'allCoveringSheets_hasGroupoid hSmooth'
FACT_VARIABLE = 'variable [hSmooth : Fact SmoothTransitionResidual]'
FACT_NAMED_VARIABLE = 'variable [smoothFact : Fact SmoothTransitionResidual]'

VARIANTS = {
    'fact_binder': (FACT_VARIABLE, 'allCoveringSheets_hasGroupoid hSmooth.out'),
    'fact_named': (FACT_NAMED_VARIABLE, 'allCoveringSheets_hasGroupoid smoothFact.out'),
    'raw_instance_binder': ('variable [hSmooth : SmoothTransitionResidual]', RAW_USE),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def audit(text: str) -> dict[str, int]:
    return {
        'sorry': len(re.findall(r'\bsorry\b', text)),
        'admit': len(re.findall(r'\badmit\b', text)),
        'native_decide': len(re.findall(r'\bnative_decide\b', text)),
        'Lean.ofReduceBool': text.count('Lean.ofReduceBool'),
        'global_axiom': len(re.findall(r'(?m)^\s*axiom\s+', text)),
        'unsafe': len(re.findall(r'(?m)^\s*unsafe\s+', text)),
        'maxHeartbeats_zero': len(re.findall(r'set_option\s+maxHeartbeats\s+0\b', text)),
    }


def replace_exact_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'expected one {label}, found {count}')
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) not in (3, 4):
        raise SystemExit('usage: qym_patch_v13_groupoid_fact.py VARIANT QYM.lean [EXPECTED_SHA256]')
    variant, filename = sys.argv[1], sys.argv[2]
    expected_sha = sys.argv[3] if len(sys.argv) == 4 else None
    if variant not in VARIANTS:
        raise SystemExit(f'unknown variant {variant!r}')
    path = Path(filename)
    before = path.read_bytes()
    if expected_sha is not None and sha256(before) != expected_sha:
        raise SystemExit(f'unexpected input SHA256: {sha256(before)} != {expected_sha}')
    text = before.decode('utf-8')
    section_start = text.find('section ConditionalSmoothAtlas')
    section_end = text.find('end ConditionalSmoothAtlas', section_start)
    if section_start < 0 or section_end < 0:
        raise SystemExit('conditional atlas section missing')
    prefix, section, suffix = text[:section_start], text[section_start:section_end], text[section_end:]
    before_audit = audit(text)
    variable_line, use_line = VARIANTS[variant]
    section = replace_exact_once(section, RAW_VARIABLE, variable_line, 'section variable')
    section = replace_exact_once(section, RAW_USE, use_line, 'groupoid witness use')
    text = prefix + section + suffix
    after_audit = audit(text)
    if after_audit != before_audit:
        raise SystemExit(f'forbidden-token delta: {before_audit} -> {after_audit}')
    path.write_text(text, encoding='utf-8')
    after = path.read_bytes()
    marker = 'def CuspCollarResidual'
    marker_index = text.find(marker)
    if marker_index < 0:
        raise SystemExit('post-V13 gate marker missing')
    print(json.dumps({
        'schema': 'qym-v13-groupoid-fact-patch-v1',
        'variant': variant,
        'input_sha256': sha256(before),
        'input_blob': git_blob(before),
        'candidate_sha256': sha256(after),
        'candidate_blob': git_blob(after),
        'bytes': len(after),
        'lf': after.count(b'\n'),
        'gate_line': text.count('\n', 0, marker_index) + 1,
        'forbidden': after_audit,
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
