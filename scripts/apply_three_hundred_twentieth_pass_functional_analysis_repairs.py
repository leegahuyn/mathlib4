from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
from pathlib import Path
import re
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "171588d37133a6494727645474dadad3f80828bdcf8a1ce5b8fd72b77d4d3c0a"
EXPECTED_OUTPUT_SHA256 = "db9710d2f2c509ac28edfb71b84f6d6bc339526ffa81578467a25493a55e2136"
DIFF_SHA256 = "3d8ad78ce16086dbd1e05fe7a2e1346c5949486c1a0481063f6db4dc028f3301"
DIFF_ZLIB_B64 = (
    "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"
)

HUNK_RE = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def digest(data: bytes) -> str:
    return sha256(data).hexdigest()


def apply_unified_diff(original: str, patch: str) -> str:
    old = original.splitlines(keepends=True)
    out: list[str] = []
    old_index = 0
    lines = patch.splitlines(keepends=True)
    i = 0
    while i < len(lines) and not lines[i].startswith("@@ "):
        i += 1
    hunk_no = 0
    while i < len(lines):
        match = HUNK_RE.match(lines[i])
        if match is None:
            raise RuntimeError(f"invalid unified-diff hunk header: {lines[i]!r}")
        hunk_no += 1
        old_start = int(match.group(1))
        old_count = int(match.group(2) or "1")
        new_count = int(match.group(4) or "1")
        target_index = old_start - 1
        if target_index < old_index:
            raise RuntimeError(f"overlapping hunk {hunk_no}")
        out.extend(old[old_index:target_index])
        old_index = target_index
        consumed_old = 0
        produced_new = 0
        i += 1
        while i < len(lines) and not lines[i].startswith("@@ "):
            line = lines[i]
            if line.startswith(r"\ No newline at end of file"):
                i += 1
                continue
            if not line:
                raise RuntimeError(f"empty patch line in hunk {hunk_no}")
            tag, body = line[0], line[1:]
            if tag == " ":
                if old_index >= len(old) or old[old_index] != body:
                    got = None if old_index >= len(old) else old[old_index]
                    raise RuntimeError(
                        f"hunk {hunk_no} context mismatch at source line {old_index + 1}: "
                        f"expected {body!r}, found {got!r}"
                    )
                out.append(body)
                old_index += 1
                consumed_old += 1
                produced_new += 1
            elif tag == "-":
                if old_index >= len(old) or old[old_index] != body:
                    got = None if old_index >= len(old) else old[old_index]
                    raise RuntimeError(
                        f"hunk {hunk_no} removal mismatch at source line {old_index + 1}: "
                        f"expected {body!r}, found {got!r}"
                    )
                old_index += 1
                consumed_old += 1
            elif tag == "+":
                out.append(body)
                produced_new += 1
            else:
                raise RuntimeError(f"invalid patch tag {tag!r} in hunk {hunk_no}")
            i += 1
        if consumed_old != old_count or produced_new != new_count:
            raise RuntimeError(
                f"hunk {hunk_no} count mismatch: old {consumed_old}/{old_count}, "
                f"new {produced_new}/{new_count}"
            )
    out.extend(old[old_index:])
    return "".join(out)


def main() -> int:
    source = TARGET.read_bytes()
    input_sha = digest(source)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass320] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected FunctionalAnalysis input: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    patch_bytes = decompress(b64decode(DIFF_ZLIB_B64))
    if digest(patch_bytes) != DIFF_SHA256:
        raise RuntimeError("embedded pass320 diff checksum mismatch")
    repaired = apply_unified_diff(source.decode("utf-8"), patch_bytes.decode("utf-8"))
    repaired_bytes = repaired.encode("utf-8")
    output_sha = digest(repaired_bytes)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"pass320 output mismatch: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_bytes(repaired_bytes)
    print("[pass320] FunctionalAnalysis canonical subtype, completion, rank-one, scope, and namespace frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
