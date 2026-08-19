#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib, json, re, sys

BASE_SHA = 'c1498d669d3f43cda50edf7b61b33c865b00f6fe65ea95d9f1ab3c07794d1235'
BASE_BLOB = '75c2eab05b4298d94246a6b0757f98a6ff5c02fe'
VARIANTS = {
    'groupoid_instances',
    'groupoid_instances_fact',
    'explicit_contdiff_intermediate',
    'explicit_upper_intermediate',
    'all_instances_contdiff',
    'all_instances_upper',
}

SECTION_START = 'section ConditionalSmoothAtlas'
SECTION_END = 'end ConditionalSmoothAtlas'
CHARTED_RE = re.compile(
    r'''local instance conditionalChartedSpaceComplex\s*:\s*\n\s*ChartedSpace ℂ GammaTwoQuotient\s*:=\s*\n\s*ChartedSpace\.comp ℂ ℍ GammaTwoQuotient''',
    re.M,
)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob(data: bytes) -> str:
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


def exact_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'{label}: expected one match, got {count}')
    return text.replace(old, new, 1)


def main() -> None:
    if len(sys.argv) != 4 or sys.argv[1] not in VARIANTS:
        raise SystemExit('usage: patch.py VARIANT QYM.lean EXPECTED_SHA256')
    variant, filename, expected = sys.argv[1], Path(sys.argv[2]), sys.argv[3]
    before = filename.read_bytes()
    if sha(before) != expected or expected != BASE_SHA or blob(before) != BASE_BLOB:
        raise SystemExit(f'authority mismatch sha={sha(before)} blob={blob(before)}')
    source = before.decode('utf-8')
    start = source.find(SECTION_START)
    end = source.find(SECTION_END, start)
    if start < 0 or end < 0:
        raise SystemExit('ConditionalSmoothAtlas section not found')
    end += len(SECTION_END)
    prefix, section, suffix = source[:start], source[start:end], source[end:]
    a0 = audit(source)

    if variant in {'groupoid_instances', 'groupoid_instances_fact', 'all_instances_contdiff', 'all_instances_upper'}:
        section = exact_once(
            section,
            'private theorem conditionalHasGroupoidH :',
            'local instance conditionalHasGroupoidH :',
            'conditionalHasGroupoidH kind',
        )
        section = exact_once(
            section,
            'private theorem conditionalHasGroupoidComplex :',
            'local instance conditionalHasGroupoidComplex :',
            'conditionalHasGroupoidComplex kind',
        )

    if variant in {'groupoid_instances_fact', 'all_instances_contdiff', 'all_instances_upper'}:
        anchor = 'include hSmooth\n\n'
        insertion = (
            'include hSmooth\n\n'
            'local instance conditionalSmoothTransitionFact :\n'
            '    Fact SmoothTransitionResidual := ⟨hSmooth⟩\n\n'
        )
        section = exact_once(section, anchor, insertion, 'smooth fact anchor')

    if variant in {'explicit_contdiff_intermediate', 'all_instances_contdiff'}:
        replacement = '''local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient := by
  letI : HasGroupoid ℍ (contDiffGroupoid ∞ 𝓘(ℂ)) := by
    infer_instance
  exact ChartedSpace.comp ℂ ℍ GammaTwoQuotient'''
        matches = list(CHARTED_RE.finditer(section))
        if len(matches) != 1:
            raise SystemExit(f'charted-space declaration matches={len(matches)}')
        section = CHARTED_RE.sub(replacement, section, count=1)

    if variant in {'explicit_upper_intermediate', 'all_instances_upper'}:
        replacement = '''local instance conditionalChartedSpaceComplex :
    ChartedSpace ℂ GammaTwoQuotient := by
  letI : HasGroupoid ℍ upperHalfPlaneSmoothGroupoid := by
    infer_instance
  exact ChartedSpace.comp ℂ ℍ GammaTwoQuotient'''
        matches = list(CHARTED_RE.finditer(section))
        if len(matches) != 1:
            raise SystemExit(f'charted-space declaration matches={len(matches)}')
        section = CHARTED_RE.sub(replacement, section, count=1)

    text = prefix + section + suffix
    a1 = audit(text)
    if a1 != a0:
        raise SystemExit(f'forbidden-token delta {a0} -> {a1}')
    filename.write_text(text, encoding='utf-8')
    after = filename.read_bytes()
    section_start_line = text.count('\n', 0, start) + 1
    section_end_index = text.find(SECTION_END, start) + len(SECTION_END)
    section_end_line = text.count('\n', 0, section_end_index) + 1
    print(json.dumps({
        'schema': 'qym-gb78-v13-groupoid-patch-v1',
        'variant': variant,
        'input_sha256': sha(before),
        'input_blob': blob(before),
        'candidate_sha256': sha(after),
        'candidate_blob': blob(after),
        'section_start_line': section_start_line,
        'section_end_line': section_end_line,
        'forbidden': a1,
        'bytes': len(after),
        'lf': after.count(b'\n'),
    }, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
