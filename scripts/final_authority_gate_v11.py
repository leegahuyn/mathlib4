#!/usr/bin/env python3
"""Final-authority v11: retain v5 policy and align project objects with LEAN_PATH.

The aggregate BuildAll blocker is an object-layout failure, not a mathematical
failure: prior direct compiles emitted project `.olean`/`.ilean` files beside
sources, whereas `lake env lean` resolves local imports from
`.lake/build/lib/lean`.  This wrapper executes the current checked-in v5 policy
and changes only those runtime object paths and the matching clean removal.

Set `FINAL_AUTHORITY_OBJECT_LAYOUT=0` to run the same policy without the layout
repair.  The V11 workflow uses that mode for the mandatory initial full-build
reproduction, then uses the default repaired mode for the complete rebuild.
"""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
V5 = ROOT / "scripts" / "final_authority_gate_v5.py"
wrapper_source = V5.read_text(encoding="utf-8")

# Inject into v5 immediately after it reads the canonical controller source.
# The injected code executes before v5 applies its existing policy replacements.
injection_code = r'''
import os as _final_authority_v11_os
import re as _final_authority_v11_re

if _final_authority_v11_os.environ.get("FINAL_AUTHORITY_OBJECT_LAYOUT", "1") != "0":
    _object_pattern = _final_authority_v11_re.compile(
        r'(?m)^(?P<i>[ \t]*)olean = ROOT / path\.with_suffix\("\.olean"\)\n'
        r'(?P=i)ilean = ROOT / path\.with_suffix\("\.ilean"\)\n'
    )

    def _object_replacement(_match):
        _indent = _match.group("i")
        return (
            f'{_indent}object_root = ROOT / ".lake" / "build" / "lib" / "lean"\n'
            f'{_indent}olean = object_root / path.with_suffix(".olean")\n'
            f'{_indent}ilean = object_root / path.with_suffix(".ilean")\n'
            f'{_indent}olean.parent.mkdir(parents=True, exist_ok=True)\n'
        )

    source, _object_count = _object_pattern.subn(
        _object_replacement, source, count=1
    )
    if _object_count != 1:
        raise RuntimeError(
            "v11 object-layout patch expected exactly one compile_one assignment "
            f"pair, found {_object_count}"
        )

    _clean_old = '    removed = clear_objects(paths) if clean_first else []\n'
    _clean_new = (
        '    removed = clear_objects(paths) if clean_first else []\n'
        '    if clean_first:\n'
        '        object_root = ROOT / ".lake" / "build" / "lib" / "lean"\n'
        '        for clean_path in paths:\n'
        '            for clean_ext in (".olean", ".ilean"):\n'
        '                clean_object = object_root / clean_path.with_suffix(clean_ext)\n'
        '                if clean_object.exists():\n'
        '                    clean_object.unlink()\n'
        '                    removed.append(str(clean_object.relative_to(ROOT)))\n'
    )
    if source.count(_clean_old) != 1:
        raise RuntimeError(
            "v11 clean-layout patch expected exactly one compile_sequence marker, "
            f"found {source.count(_clean_old)}"
        )
    source = source.replace(_clean_old, _clean_new, 1)
'''

read_marker = 'source = ORIGINAL.read_text(encoding="utf-8")\n'
if wrapper_source.count(read_marker) != 1:
    raise RuntimeError(
        "v11 v5 injection point expected exactly once, "
        f"found {wrapper_source.count(read_marker)}"
    )
wrapper_source = wrapper_source.replace(
    read_marker, read_marker + injection_code, 1
)

# Extend only the v5 changed-path allowlist.  This does not relax protection of
# FA, Integrated, QYM, or any other mathematical root.
allow_marker = '        "scripts/final_authority_gate_v5.py",\\n'
allow_extras = [
    "scripts/final_authority_gate_v10.py",
    "scripts/final_authority_gate_v11.py",
    "final_authority_buildall_v9_trigger.txt",
    "final_authority_buildall_v10_trigger.txt",
    "final_authority_buildall_v11_trigger.txt",
]
missing_extras = [name for name in allow_extras if name not in wrapper_source]
if missing_extras:
    if wrapper_source.count(allow_marker) != 1:
        raise RuntimeError(
            "v11 allowlist marker expected exactly once, "
            f"found {wrapper_source.count(allow_marker)}"
        )
    extension = allow_marker + "".join(
        f'        "{name}",\\n' for name in missing_extras
    )
    wrapper_source = wrapper_source.replace(allow_marker, extension, 1)

namespace = {
    "__name__": "__main__",
    "__file__": str(V5),
    "__package__": None,
}
exec(compile(wrapper_source, str(V5), "exec"), namespace, namespace)
