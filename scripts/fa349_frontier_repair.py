from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "2c4376b7b6adaabe7917bbfbc327c622da252a585835461881a9e3ac336dc607"
EXPECTED_OUTPUT_SHA256 = "2facdbe0afb09d0cd4771a517188591e7aca619832cd89f3ba30e35ec91e6609"
PAYLOAD = """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"""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass349] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected PASS 349 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    lines = text.splitlines(keepends=True)
    operations = json.loads(decompress(b64decode(PAYLOAD)).decode("utf-8"))
    print(f"line_operations={len(operations)}")
    for start, stop, replacement in reversed(operations):
        lines[start:stop] = replacement
    output = "".join(lines)
    output_sha = digest(output)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected PASS 349 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )
    TARGET.write_text(output, encoding="utf-8")
    print("[pass349] domRestrict, covariance, cutoff, density, closure, and fixed-phase analytic frontiers repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
