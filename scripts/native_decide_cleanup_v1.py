#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

FILES = {
    Path("PrimalitySheafVerification/Spt1.lean"): "ed554b8268e9504281572d0cea27e40d5ba06a19",
    Path("PrimalitySheafVerification/Mock1_Advanced.lean"): "2dc68bb04df549064b41fc318d18ea02d4d40679",
}
TOKEN = "native_decide"
REPLACEMENT = "decide"


def git_blob(path: Path) -> str:
    return subprocess.check_output(["git", "hash-object", str(path)], text=True).strip()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_noncode(text: str) -> str:
    out = list(text)
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(out):
        if depth:
            if text.startswith("/-", i):
                out[i] = out[i + 1] = " "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out[i] = out[i + 1] = " "
                depth -= 1
                i += 2
                continue
            if out[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if in_string:
            ch = out[i]
            if ch != "\n":
                out[i] = " "
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            out[i] = out[i + 1] = " "
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(out) and out[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if out[i] == '"':
            out[i] = " "
            in_string = True
        i += 1
    if depth != 0 or in_string:
        raise SystemExit("unterminated comment or string while auditing Lean source")
    return "".join(out)


def token_count(text: str) -> int:
    code = strip_noncode(text)
    return len(re.findall(r"(?<![A-Za-z0-9_])native_decide(?![A-Za-z0-9_])", code))


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: native_decide_cleanup_v1.py REPORT.json")
    report_path = Path(sys.argv[1])
    report_path.parent.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, object]] = []

    for path, expected_blob in FILES.items():
        if not path.is_file():
            raise SystemExit(f"missing source: {path}")
        observed_blob = git_blob(path)
        if observed_blob != expected_blob:
            raise SystemExit(
                f"wrong source blob for {path}: expected {expected_blob}, got {observed_blob}"
            )
        before_text = path.read_text()
        before_code_count = token_count(before_text)
        before_text_count = before_text.count(TOKEN)
        if before_code_count == 0:
            raise SystemExit(f"no executable {TOKEN} found in {path}")

        after_text = before_text.replace(TOKEN, REPLACEMENT)
        path.write_text(after_text)
        after_code_count = token_count(after_text)
        if after_code_count != 0 or TOKEN in after_text:
            raise SystemExit(f"failed to remove all {TOKEN} occurrences from {path}")

        rows.append(
            {
                "file": str(path),
                "before_blob": expected_blob,
                "before_sha256": hashlib.sha256(before_text.encode()).hexdigest(),
                "before_executable_count": before_code_count,
                "before_text_count": before_text_count,
                "after_blob": git_blob(path),
                "after_sha256": sha256(path),
                "after_executable_count": after_code_count,
                "replacement": REPLACEMENT,
            }
        )

    report = {
        "schema": "native-decide-cleanup-v1",
        "files": rows,
        "total_before_executable_count": sum(
            int(row["before_executable_count"]) for row in rows
        ),
        "total_after_executable_count": sum(
            int(row["after_executable_count"]) for row in rows
        ),
        "all_removed": all(int(row["after_executable_count"]) == 0 for row in rows),
    }
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
