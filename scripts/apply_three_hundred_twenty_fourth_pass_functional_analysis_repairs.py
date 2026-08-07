from __future__ import annotations

from pathlib import Path
import base64
import hashlib
import re
import zlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "41a542e802bbb2b05e56f81ae5b94c045cde75b14b140b679cc4ed70e156b960"
EXPECTED_OUTPUT_SHA256 = "cbe40f444a0fd843f89f87608b5f962cad774375d5daadf124b62ab155165350"
DIFF_SHA256 = "17759d25120881ed134070d60a44a05efed0cd79a6e34d0bdf837f204d9f9d75"
DIFF_ZLIB_B64 = (
    "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"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def parse_hunks(diff: str):
    lines = diff.splitlines(keepends=True)
    index = 0
    while index < len(lines):
        if not lines[index].startswith("@@ "):
            index += 1
            continue
        match = re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", lines[index])
        if match is None:
            raise RuntimeError(f"malformed hunk header: {lines[index]!r}")
        old_start = int(match.group(1))
        index += 1
        old_lines: list[str] = []
        new_lines: list[str] = []
        while index < len(lines) and not lines[index].startswith("@@ "):
            line = lines[index]
            if line.startswith(" "):
                old_lines.append(line[1:])
                new_lines.append(line[1:])
            elif line.startswith("-"):
                old_lines.append(line[1:])
            elif line.startswith("+"):
                new_lines.append(line[1:])
            elif line.startswith("\\ No newline"):
                pass
            else:
                break
            index += 1
        yield old_start, "".join(old_lines), "".join(new_lines)


def apply_strict_unified_diff(source: str, diff: str) -> str:
    cursor = 0
    count = 0
    for hunk_index, (old_start, old, new) in enumerate(parse_hunks(diff), 1):
        count = hunk_index
        matches: list[int] = []
        position = source.find(old, cursor)
        while position != -1:
            matches.append(position)
            position = source.find(old, position + 1)
        if len(matches) != 1:
            global_matches: list[int] = []
            position = source.find(old)
            while position != -1:
                global_matches.append(position)
                position = source.find(old, position + 1)
            raise RuntimeError(
                f"pass324 hunk {hunk_index} at original line {old_start}: "
                f"expected one forward match, found {len(matches)}; "
                f"global matches={len(global_matches)}"
            )
        position = matches[0]
        source = source[:position] + new + source[position + len(old):]
        cursor = position + len(new)
        print(f"pass324 hunk {hunk_index}: original_line={old_start}")
    if count != 13:
        raise RuntimeError(f"expected 13 pass324 hunks, found {count}")
    return source


def main() -> int:
    source = TARGET.read_text(encoding="utf-8")
    input_sha = sha256_text(source)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass324] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass324 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    compressed = base64.b64decode(DIFF_ZLIB_B64, validate=True)
    diff_bytes = zlib.decompress(compressed)
    actual_diff_sha = sha256_bytes(diff_bytes)
    print(f"diff_sha256={actual_diff_sha}")
    if actual_diff_sha != DIFF_SHA256:
        raise RuntimeError(
            f"corrupt pass324 diff payload: {actual_diff_sha}; expected {DIFF_SHA256}"
        )

    repaired = apply_strict_unified_diff(source, diff_bytes.decode("utf-8"))
    output_sha = sha256_text(repaired)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass324 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(repaired, encoding="utf-8")
    print("[pass324] FunctionalAnalysis first proof/API frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
