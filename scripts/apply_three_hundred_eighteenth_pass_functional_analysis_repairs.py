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
DIFF_ZLIB_B64 = "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"


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
        match = re.match(
            r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", lines[i]
        )
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
    for index, (old_start, old, new) in enumerate(parse_hunks(diff), 1):
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
        print(
            f"pass318 hunk {index}: original_line={old_start} "
            f"old_bytes={len(old.encode('utf-8'))} "
            f"new_bytes={len(new.encode('utf-8'))}"
        )
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
            f"unexpected pass318 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    diff_bytes = zlib.decompress(base64.b64decode(DIFF_ZLIB_B64))
    actual_diff_sha = sha256_bytes(diff_bytes)
    print(f"diff_sha256={actual_diff_sha}")
    if actual_diff_sha != DIFF_SHA256:
        raise RuntimeError(
            f"corrupt pass318 diff payload: {actual_diff_sha}; "
            f"expected {DIFF_SHA256}"
        )

    repaired = apply_strict_unified_diff(source, diff_bytes.decode("utf-8"))
    output_sha = sha256_text(repaired)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass318 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(repaired, encoding="utf-8")
    print("[pass318] FunctionalAnalysis opaque-subtype and bundled-accessor frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
