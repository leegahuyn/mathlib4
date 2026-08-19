#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import sys


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: fix_qym_v6_heredoc.py WORKFLOW.yml")

    path = Path(sys.argv[1])
    before = path.read_bytes()
    lines = before.decode("utf-8").splitlines(keepends=True)
    output: list[str] = []
    patched: list[dict[str, int]] = []
    index = 0

    while index < len(lines):
        line = lines[index]
        stripped = line.lstrip(" ")
        is_target = (
            stripped.startswith('python3 - "$dir"')
            and "<<'PY'" in stripped
        )
        output.append(line)
        index += 1
        if not is_target:
            continue

        opener_line = index
        closed = False
        while index < len(lines):
            body_line = lines[index]
            body_stripped = body_line.strip()
            if body_stripped:
                leading = len(body_line) - len(body_line.lstrip(" "))
                if leading < 2:
                    raise SystemExit(
                        f"target heredoc line {index + 1} has fewer than two spaces"
                    )
                body_line = body_line[2:]
            output.append(body_line)
            index += 1
            if body_stripped == "PY":
                patched.append(
                    {"opener_line": opener_line, "closer_line": index}
                )
                closed = True
                break
        if not closed:
            raise SystemExit(f"unterminated target heredoc at line {opener_line}")

    if len(patched) != 2:
        raise SystemExit(f"target heredoc count={len(patched)}")

    after_text = "".join(output)
    after = after_text.encode("utf-8")
    if after == before:
        raise SystemExit("workflow was not changed")

    # Both target delimiters must now align with the YAML run-block baseline.
    after_lines = after_text.splitlines()
    for item in patched:
        closer = after_lines[item["closer_line"] - 1]
        if closer != "          PY":
            raise SystemExit(
                f"unexpected corrected delimiter at line {item['closer_line']}: {closer!r}"
            )

    path.write_bytes(after)
    result = {
        "schema": "qym-v6-heredoc-indent-fix",
        "path": str(path),
        "before_sha256": sha256(before),
        "after_sha256": sha256(after),
        "patched": patched,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
