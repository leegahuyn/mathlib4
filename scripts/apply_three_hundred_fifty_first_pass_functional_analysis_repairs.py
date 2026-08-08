from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "519d8b37b8fe03fedfd61d8afd60be98e9ac42e6eaee5dcf25a82891f18e80da"
EXPECTED_OUTPUT_SHA256 = "8831fff80c528bccdd9f7f4a57e1f61703aab00e680bcad6f34feeddaab24039"
PAYLOAD = """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"""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass351] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass351 input sha256: {input_sha}; expected {EXPECTED_INPUT_SHA256}"
        )

    lines = text.splitlines(keepends=True)
    hunks = json.loads(decompress(b64decode(PAYLOAD)).decode("utf-8"))
    for idx, hunk in enumerate(reversed(hunks), 1):
        i1 = int(hunk["i1"])
        old = hunk["old"]
        new = hunk["new"]
        old_lines = old.splitlines(keepends=True)
        actual = "".join(lines[i1:i1 + len(old_lines)])
        if actual != old:
            raise RuntimeError(
                f"pass351 hunk {len(hunks) - idx + 1} mismatch at original line {i1 + 1}"
            )
        lines[i1:i1 + len(old_lines)] = new.splitlines(keepends=True)
        print(f"pass351 hunk {len(hunks) - idx + 1}: original_line={i1 + 1}")

    output = "".join(lines)
    output_sha = digest(output)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass351 output sha256: {output_sha}; expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(output, encoding="utf-8")
    print("[pass351] FunctionalAnalysis prefix root repairs applied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
