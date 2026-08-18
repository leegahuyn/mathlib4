#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import collections
import hashlib
import json
import os
import re
import sys


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qym_auto_producer_summarize.py OUT VARIANT")
    out = Path(sys.argv[1])
    variant = sys.argv[2]
    raw = (out / "QYM.log").read_bytes() if (out / "QYM.log").exists() else b""
    text = raw.decode(errors="replace")
    pattern = re.compile(
        r"^(?P<file>.*?\.lean):(?P<line>\d+):(?P<column>\d+): "
        r"(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$",
        re.M,
    )
    rows: list[dict] = []
    for match in pattern.finditer(text):
        row = match.groupdict()
        row["line"] = int(row["line"])
        row["column"] = int(row["column"])
        rows.append(row)
    errors = [row for row in rows if row["severity"] == "error"]
    warnings = [row for row in rows if row["severity"] == "warning"]
    panics = re.findall(
        r"(?im)^.*(?:internal error|uncaught exception|panic(?:!|:|\s)).*$", text
    )
    exit_code = int((out / "QYM.exit").read_text().strip()) if (out / "QYM.exit").exists() else None
    baseline = json.loads((out / "BASELINE_RESULT.json").read_text(encoding="utf-8"))
    patch = json.loads((out / "PATCH_RESULT.json").read_text(encoding="utf-8"))
    result = {
        "schema": "qym-auto-producer-result-v2",
        "github_sha": os.environ.get("GITHUB_SHA"),
        "variant": variant,
        "owner": patch.get("owner"),
        "baseline_qym_sha256": baseline.get("candidate_qym_sha256"),
        "baseline_error_headers": baseline.get("error_headers"),
        "candidate_qym_sha256": patch.get("candidate_qym_sha256"),
        "candidate_qym_blob": patch.get("candidate_qym_blob"),
        "exit": exit_code,
        "error_headers": len(errors),
        "warning_headers": len(warnings),
        "error_codes": dict(
            sorted(collections.Counter(row.get("code") or "uncoded" for row in errors).items())
        ),
        "first_error": errors[0] if errors else None,
        "last_error": errors[-1] if errors else None,
        "panic_lines": len(panics),
        "log_sha256": hashlib.sha256(raw).hexdigest(),
        "semantic_pass": exit_code == 0 and not errors and not panics,
    }
    (out / "QYM.diagnostics.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8"
    )
    (out / "QYM.error-headers.txt").write_text(
        "".join(
            f"{row['file']}:{row['line']}:{row['column']}: error"
            f"{('(' + row['code'] + ')') if row.get('code') else ''}: {row['message']}\n"
            for row in errors
        ),
        encoding="utf-8",
    )
    (out / "QYM.panic-lines.txt").write_text(
        "".join(line + "\n" for line in panics), encoding="utf-8"
    )
    (out / "PROBE_RESULT.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
