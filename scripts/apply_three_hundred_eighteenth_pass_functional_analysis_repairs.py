from __future__ import annotations

from pathlib import Path
import base64
import hashlib
import re
import zlib

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "bdcafba53aabd845cb860e0e3bd59b43a547da9f7d50810dcd3b4ad91819201b"
EXPECTED_OUTPUT_SHA256 = "a61e8c20bdc28395d6b71857ec714780e36e8d98233480226e0442098ae3a438"
DIFF_SHA256 = "687e3ac919719702580f9f778c224468d5323df3716c964fc40f3f3e774b9b01"
DIFF_ZLIB_B64 = (
    "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"
    "8fl/u1IG7Q=="
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def parse_hunks(diff: str):
    lines = diff.splitlines(keepends=True)
    i = 0
    while i < len(lines):
        if not lines[i].startswith("@@ "):
            i += 1
            continue
        match = re.match(r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", lines[i])
        if match is None:
            raise RuntimeError(f"malformed hunk header: {lines[i]!r}")
        old_start = int(match.group(1))
        i += 1
        old_lines: list[str] = []
        new_lines: list[str] = []
        while i < len(lines) and not lines[i].startswith("@@ "):
            line = lines[i]
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
            i += 1
        yield old_start, "".join(old_lines), "".join(new_lines)


def apply_strict_unified_diff(source: str, diff: str) -> str:
    cursor = 0
    count = 0
    for index, (old_start, old, new) in enumerate(parse_hunks(diff), 1):
        count = index
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
                f"pass318 hunk {index} at original line {old_start}: "
                f"expected one forward match, found {len(matches)}; "
                f"global matches={len(global_matches)}"
            )
        position = matches[0]
        source = source[:position] + new + source[position + len(old):]
        cursor = position + len(new)
        print(f"pass318 hunk {index}: original_line={old_start}")
    if count != 18:
        raise RuntimeError(f"expected 18 pass318 hunks, found {count}")
    return source


def main() -> int:
    source = TARGET.read_text(encoding="utf-8")
    input_sha = sha256_text(source)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass318] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass318 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    compressed = base64.b64decode(DIFF_ZLIB_B64, validate=True)
    diff_bytes = zlib.decompress(compressed)
    actual_diff_sha = sha256_bytes(diff_bytes)
    print(f"diff_sha256={actual_diff_sha}")
    if actual_diff_sha != DIFF_SHA256:
        raise RuntimeError(
            f"corrupt pass318 diff payload: {actual_diff_sha}; expected {DIFF_SHA256}"
        )

    repaired = apply_strict_unified_diff(source, diff_bytes.decode("utf-8"))
    output_sha = sha256_text(repaired)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass318 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(repaired, encoding="utf-8")
    print("[pass318] FunctionalAnalysis opaque-subtype and bundled-accessor frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
