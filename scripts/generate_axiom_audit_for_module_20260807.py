#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path

from focused_source_audit_20260807 import strip_comments_and_strings
from generate_focused_axiom_audit_20260807 import declarations


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--import-module', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('files', nargs='+')
    args = parser.parse_args()

    names: list[str] = []
    for raw in args.files:
        # Validate the source scanner on every file before extracting names.
        strip_comments_and_strings(Path(raw).read_text(encoding='utf-8'))
        for name in declarations(Path(raw)):
            if name not in names:
                names.append(name)
    if not names:
        raise SystemExit('no public theorem/lemma declarations found')

    lines = [
        f'import {args.import_module}',
        '',
        'set_option pp.universes true',
        'set_option pp.explicit true',
        '',
    ]
    lines.extend(f'#print axioms {name}' for name in names)
    lines.append('')
    Path(args.output).write_text('\n'.join(lines), encoding='utf-8')
    print(f'generated_declaration_count={len(names)}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
