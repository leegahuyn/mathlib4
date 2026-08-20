#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
SOURCE = ROOT / "PrimalitySheafVerification/Mock2_FunctionalAnalysis.lean"
OUT = ROOT / "build-logs/fa448-diagnostic"
LOG = OUT / "Mock2_FunctionalAnalysis.log"
DECL_RE = re.compile(
    r"^(?:protected\s+|private\s+|noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([^\s(:]+)"
)
ERROR_RE = re.compile(
    r"(?m)^(?P<prefix>.*?Mock2_FunctionalAnalysis\.lean):"
    r"(?P<line>\d+):(?P<col>\d+):\s+error:\s*(?P<message>.*)$"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_rows(lines: list[str]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, line in enumerate(lines, start=1):
        match = DECL_RE.match(line)
        if match:
            rows.append({"name": match.group(1), "line": index})
    return rows


def declaration_at(rows: list[dict[str, Any]], line: int) -> dict[str, Any]:
    current = {"name": "<unknown>", "line": 0, "index": -1}
    for index, row in enumerate(rows):
        if int(row["line"]) > line:
            break
        current = {"name": row["name"], "line": row["line"], "index": index}
    return current


def extract_error_message(log: str, match: re.Match[str], next_start: int) -> str:
    chunk = log[match.start("message") : next_start]
    kept: list[str] = []
    for index, raw in enumerate(chunk.splitlines()):
        if index > 0 and re.match(
            r"^.*\.lean:\d+:\d+:\s+(?:error|warning):", raw
        ):
            break
        kept.append(raw.rstrip())
        if len("\n".join(kept)) >= 5000:
            break
    return "\n".join(kept).strip()[:5000]


def numbered_context(lines: list[str], center: int, radius: int = 16) -> str:
    start = max(1, center - radius)
    end = min(len(lines), center + radius)
    return "\n".join(
        f"{line_number:6d} | {lines[line_number - 1]}"
        for line_number in range(start, end + 1)
    )


def declaration_block(
    lines: list[str], rows: list[dict[str, Any]], declaration_index: int
) -> str:
    if declaration_index < 0 or declaration_index >= len(rows):
        return ""
    start = int(rows[declaration_index]["line"])
    end = (
        int(rows[declaration_index + 1]["line"]) - 1
        if declaration_index + 1 < len(rows)
        else len(lines)
    )
    # Bound very large blocks while retaining both start and error-adjacent context.
    if end - start + 1 > 450:
        end = start + 449
    return "\n".join(
        f"{line_number:6d} | {lines[line_number - 1]}"
        for line_number in range(start, end + 1)
    )


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    source_data = SOURCE.read_bytes()
    source_text = source_data.decode("utf-8", errors="replace")
    lines = source_text.splitlines()
    rows = declaration_rows(lines)
    log = LOG.read_text(encoding="utf-8", errors="replace") if LOG.exists() else ""
    matches = list(ERROR_RE.finditer(log))

    errors: list[dict[str, Any]] = []
    for index, match in enumerate(matches[:300]):
        next_start = matches[index + 1].start() if index + 1 < len(matches) else len(log)
        line = int(match.group("line"))
        col = int(match.group("col"))
        decl = declaration_at(rows, line)
        errors.append(
            {
                "ordinal": index + 1,
                "line": line,
                "column": col,
                "message": extract_error_message(log, match, next_start),
                "declaration": decl["name"],
                "declaration_line": decl["line"],
                "declaration_index": decl["index"],
            }
        )

    metadata: dict[str, Any] = {
        "classification": "LEAN_FAILURE" if errors else "NO_PARSED_ERROR",
        "source_path": str(SOURCE.relative_to(ROOT)),
        "source_sha256": sha256(source_data),
        "line_count": len(lines),
        "declaration_count": len(rows),
        "error_headers_captured": len(matches),
        "errors_recorded": len(errors),
        "first_error": errors[0] if errors else None,
        "Mock2_exit": (OUT / "Mock2.exit").read_text().strip()
        if (OUT / "Mock2.exit").exists()
        else "missing",
        "Mock2_Advanced_exit": (OUT / "Mock2_Advanced.exit").read_text().strip()
        if (OUT / "Mock2_Advanced.exit").exists()
        else "missing",
        "FA_exit": (OUT / "Mock2_FunctionalAnalysis.exit").read_text().strip()
        if (OUT / "Mock2_FunctionalAnalysis.exit").exists()
        else "missing",
        "Lean_version": (OUT / "lean-version.txt").read_text().strip()
        if (OUT / "lean-version.txt").exists()
        else "missing",
        "Lake_version": (OUT / "lake-version.txt").read_text().strip()
        if (OUT / "lake-version.txt").exists()
        else "missing",
        "repository_head": (OUT / "repository-head.txt").read_text().strip()
        if (OUT / "repository-head.txt").exists()
        else "missing",
        "lake_manifest_sha256": sha256((ROOT / "lake-manifest.json").read_bytes())
        if (ROOT / "lake-manifest.json").exists()
        else "missing",
    }
    (OUT / "DIAGNOSTIC.json").write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    (OUT / "ERRORS.json").write_text(
        json.dumps(errors, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )

    contexts: list[str] = []
    seen_contexts: set[tuple[int, int]] = set()
    for error in errors[:80]:
        key = (int(error["line"]), int(error["column"]))
        if key in seen_contexts:
            continue
        seen_contexts.add(key)
        contexts.extend(
            [
                "=" * 100,
                (
                    f"ERROR {error['ordinal']}: {error['line']}:{error['column']} "
                    f"declaration={error['declaration']} "
                    f"declaration_index={error['declaration_index']}"
                ),
                str(error["message"]),
                "-" * 100,
                numbered_context(lines, int(error["line"])),
                "",
            ]
        )
    (OUT / "ERROR_CONTEXTS.txt").write_text(
        "\n".join(contexts) + "\n", encoding="utf-8"
    )

    blocks: list[str] = []
    seen_declarations: set[int] = set()
    for error in errors[:80]:
        decl_index = int(error["declaration_index"])
        if decl_index in seen_declarations:
            continue
        seen_declarations.add(decl_index)
        blocks.extend(
            [
                "=" * 100,
                (
                    f"DECLARATION {error['declaration']} index={decl_index} "
                    f"starts={error['declaration_line']} first_error={error['line']}:{error['column']}"
                ),
                declaration_block(lines, rows, decl_index),
                "",
            ]
        )
    (OUT / "ERROR_DECLARATION_BLOCKS.txt").write_text(
        "\n".join(blocks) + "\n", encoding="utf-8"
    )

    # Always expose the current 32k/33k work region explicitly.
    region_start = 31680
    region_end = min(len(lines), 33850)
    (OUT / "SOURCE_REGION_31680_33850.txt").write_text(
        "\n".join(
            f"{line_number:6d} | {lines[line_number - 1]}"
            for line_number in range(region_start, region_end + 1)
        )
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps(metadata, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
