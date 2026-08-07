from __future__ import annotations

from base64 import b64decode
from hashlib import sha256
import json
from pathlib import Path
from zlib import decompress

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "PrimalitySheafVerification" / "Mock2_FunctionalAnalysis.lean"
EXPECTED_INPUT_SHA256 = "ff39634e079813652d3eaafee3585bec46897b5647098ebf8990991e52021e36"
EXPECTED_OUTPUT_SHA256 = "828670615f4d1fdbfb8b84240419f8a745af049729d3f30ebacfefa332d3ba2b"
PAYLOAD = """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"""


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def main() -> int:
    text = TARGET.read_text(encoding="utf-8")
    input_sha = digest(text)
    print(f"input_sha256={input_sha}")
    if input_sha == EXPECTED_OUTPUT_SHA256:
        print("[pass343-v2] already applied")
        return 0
    if input_sha != EXPECTED_INPUT_SHA256:
        raise RuntimeError(
            f"unexpected pass343-v2 input sha256: {input_sha}; "
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
            f"unexpected pass343-v2 output sha256: {output_sha}; "
            f"expected {EXPECTED_OUTPUT_SHA256}"
        )

    TARGET.write_text(text, encoding="utf-8")
    print(
        "[pass343-v2] stable-core negation, covariance, compact-tail norm, "
        "Euclidean density/integrability, embedding, gauge, and localize "
        "frontiers repaired"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
