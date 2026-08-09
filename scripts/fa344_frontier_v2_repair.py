from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "828670615f4d1fdbfb8b84240419f8a745af049729d3f30ebacfefa332d3ba2b"
EXPECTED_OUTPUT_SHA256 = "59d4bcc02ff615190da0691c9bef52fe3d8bfcb0b8cdf573c300e258757376b6"
PAYLOAD = """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"""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass344-v2] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass344-v2 input sha256: {input_sha}; "
            f"expected {EXPECTED_INPUT_SHA256}"
        )

    replacements = json.loads(decompress(b64decode(PAYLOAD)).decode("utf-8"))
    for item in replacements:
        old = item["old"]
        new = item["new"]
        expected = int(item["expected"])
        count = text.count(old)
        print(f'{item["name"]}: expected={expected} actual={count}')
        if count != expected:
            raise RuntimeError(
                f'{item["name"]}: expected {expected} occurrence(s), found {count}'
            )
        text = text.replace(old, new)

    output_sha = digest(text)
    print(f"output_sha256={output_sha}")
    if output_sha != EXPECTED_OUTPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass344-v2 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )

    TARGET.write_text(text, encoding="utf-8")
    print("[pass344-v2] fixed-phase instances and first analytic frontier repaired")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
