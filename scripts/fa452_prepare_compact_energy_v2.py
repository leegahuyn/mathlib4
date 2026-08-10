#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
spec = importlib.util.spec_from_file_location(
    "fa452_prepare_impl", ROOT / "scripts/fa452_prepare_compact_energy.py"
)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load FA452 generator implementation")
impl = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = impl
spec.loader.exec_module(impl)


def code_without_comments_or_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    line_comment = False
    block_depth = 0
    string = False
    escaped = False
    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""
        if line_comment:
            if c == "\n":
                line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if c == "/" and n == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
                continue
            if c == "-" and n == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if string:
            out.append("\n" if c == "\n" else " ")
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                string = False
            i += 1
            continue
        if c == "-" and n == "-":
            line_comment = True
            out.extend((" ", " "))
            i += 2
            continue
        if c == "/" and n == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue
        if c == '"':
            string = True
            out.append(" ")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def forbidden_counts(text: str) -> dict[str, int]:
    code = code_without_comments_or_strings(text)
    patterns = {
        "sorry": r"\bsorry\b",
        "admit": r"\badmit\b",
        "new_global_axiom": r"(?m)^\s*(?:protected\s+|private\s+)?axiom\b",
        "unsafe": r"\bunsafe\b",
        "native_decide": r"\bnative_decide\b",
        "Lean.ofReduceBool": r"\bLean\.ofReduceBool\b",
    }
    return {name: len(re.findall(pattern, code)) for name, pattern in patterns.items()}


if not hasattr(impl.base, "forbidden_counts"):
    impl.base.forbidden_counts = forbidden_counts

if __name__ == "__main__":
    impl.main()
