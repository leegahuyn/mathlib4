#!/usr/bin/env python3
"""Generate #print axioms commands for public theorem/lemma declarations.

This deliberately audits declarations from the three substantive focused source
files rather than a hand-picked sample.  The generated file imports QYM, which
loads the complete focused dependency graph.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from focused_source_audit_20260807 import strip_comments_and_strings

NAMESPACE = re.compile(r"^\s*namespace\s+([^\s]+)\s*$")
SECTION = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+[^\s]+)?\s*$")
END = re.compile(r"^\s*end(?:\s+[^\s]+)?\s*$")
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?P<mods>(?:(?:private|protected|nonrec|local)\s+)*)"
    r"(?:theorem|lemma)\s+(?P<name>[^\s:(]+)"
)


def declarations(path: Path) -> list[str]:
    code = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    namespace_parts: list[str] = []
    blocks: list[tuple[str, int]] = []
    result: list[str] = []

    for line in code.splitlines():
        match = NAMESPACE.match(line)
        if match:
            parts = [p for p in match.group(1).split(".") if p]
            namespace_parts.extend(parts)
            blocks.append(("namespace", len(parts)))
            continue
        if SECTION.match(line):
            blocks.append(("section", 0))
            continue
        if END.match(line):
            if blocks:
                kind, count = blocks.pop()
                if kind == "namespace" and count:
                    del namespace_parts[-count:]
            continue
        match = DECL.match(line)
        if not match:
            continue
        mods = match.group("mods").split()
        if "private" in mods or "local" in mods:
            continue
        raw = match.group("name")
        if raw.startswith("_root_."):
            full = raw[len("_root_.") :]
        else:
            full = ".".join([*namespace_parts, raw]) if namespace_parts else raw
        if full not in result:
            result.append(full)
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("files", nargs="+")
    args = parser.parse_args()

    names: list[str] = []
    for raw in args.files:
        for name in declarations(Path(raw)):
            if name not in names:
                names.append(name)

    output = Path(args.output)
    lines = [
        "import PrimalitySheafVerification.QYM",
        "",
        "set_option pp.universes true",
        "set_option pp.explicit true",
        "",
    ]
    for name in names:
        lines.append(f"#print axioms {name}")
    lines.append("")
    output.write_text("\n".join(lines), encoding="utf-8")
    print(f"generated_declaration_count={len(names)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
