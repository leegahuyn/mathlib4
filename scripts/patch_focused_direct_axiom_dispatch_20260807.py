#!/usr/bin/env python3
from pathlib import Path

path = Path('scripts/focused_direct_verify_20260807.sh')
text = path.read_text(encoding='utf-8')
starts = [
    '# Audit every declaration whose Lean source file is one of the three',
    '# Audit every public theorem/lemma declaration in the substantive focused modules.',
]
start = -1
for marker in starts:
    start = text.find(marker)
    if start >= 0:
        break
end = text.find('\nsha256sum \\\n', start)
if start < 0 or end < 0:
    raise SystemExit('axiom audit replacement anchors not found')
replacement = '''# Comprehensive allowed-axiom audit with a Lean-version-compatible fallback.\nbash scripts/focused_axiom_audit_dispatch_20260807.sh "${LOGDIR}"\n'''
text = text[:start] + replacement + text[end + 1:]
text = text.replace("AXIOM_GENERATOR='scripts/generate_focused_axiom_audit_20260807.py'\n", '')
text = text.replace(
    'cp /tmp/focused_axiom_audit_20260807.lean "${LOGDIR}/focused_axiom_audit_20260807.lean"\n',
    '',
)
path.write_text(text, encoding='utf-8')
if 'focused_axiom_audit_dispatch_20260807.sh' not in path.read_text(encoding='utf-8'):
    raise SystemExit('axiom dispatcher call missing')
