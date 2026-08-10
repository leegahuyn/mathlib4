#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import re
import sys
from pathlib import Path

ROOT = Path.cwd()
LEGACY = ROOT / "scripts/fa442_record_direct_metric.py"

spec = importlib.util.spec_from_file_location("fa442_metric_legacy", LEGACY)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load legacy metric recorder")
legacy = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = legacy
spec.loader.exec_module(legacy)


def proposition_header(text: str, name: str) -> str:
    """Hash the declaration proposition/type through `:=`, not proof syntax.

    This makes `:= term` and `:= by ...` equivalent for statement/header
    invariance while still rejecting any changed assumptions or conclusion.
    """
    lines = text.splitlines(keepends=True)
    start: int | None = None
    for index, line in enumerate(lines):
        match = legacy.DECL_RE.match(line)
        if match and match.group(1) == name:
            start = index
            break
    if start is None:
        return ""
    end = len(lines)
    for index in range(start + 1, len(lines)):
        if legacy.DECL_RE.match(lines[index]):
            end = index
            break
    block = "".join(lines[start:end])
    marker = block.find(":=")
    return block[: marker + len(":=")] if marker >= 0 else ""


def strict_parse_errors(stem: str):
    log_path = legacy.OUT / f"{stem}.log"
    log = legacy.read_text(log_path)
    pattern = re.compile(
        rf"(?m)^(?P<prefix>.*?{re.escape(stem)}\.lean):"
        r"(?P<line>\d+):(?P<col>\d+):\s+"
        r"error(?:\([^\)\r\n]+\))?:\s*(?P<message>.*)$"
    )
    matches = list(pattern.finditer(log))
    first_line = int(matches[0].group("line")) if matches else 0
    first_col = int(matches[0].group("col")) if matches else 0
    message = ""
    if matches:
        start = matches[0].start("message")
        end = matches[1].start() if len(matches) > 1 else len(log)
        chunk = log[start:end]
        continuation: list[str] = []
        diagnostic_header = re.compile(
            r"^.*\.lean:\d+:\d+:\s+(?:error|warning)"
            r"(?:\([^\)\r\n]+\))?:"
        )
        for index, raw in enumerate(chunk.splitlines()):
            if index > 0 and diagnostic_header.match(raw):
                break
            continuation.append(raw.rstrip())
            if len("\n".join(continuation)) >= 2000:
                break
        message = "\n".join(continuation).strip()[:2000]
    return {
        "error_headers_captured": len(matches),
        "first_line": first_line,
        "first_col": first_col,
        "first_message": message,
        "log_path": str(log_path),
    }


legacy.declaration_header = proposition_header
legacy.parse_errors = strict_parse_errors
legacy.main()
metric_path = legacy.OUT / "METRIC.json"
metric = json.loads(metric_path.read_text(encoding="utf-8"))
metric["diagnostic_parser"] = "strict_error_and_error_category_v2"
metric["header_authority"] = "declaration proposition/type through := only"
metric_path.write_text(
    json.dumps(metric, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
)
